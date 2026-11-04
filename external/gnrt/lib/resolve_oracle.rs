// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Validates GNRT's feature resolution against Guppy's Cargo Resolver V2.
//!
//! GNRT propagates feature conditions through declaration-specific isolation
//! scopes. Mistakes in this propagation can leak features between declarations
//! or route dependencies to the wrong host or target context. Guppy's CargoSet
//! supplies an independent reference, or oracle, for checking those results.
//!
//! For each comparable host/target platform, the oracle compares enabled named
//! features and dependency edges for shared, root-isolated, and closure-isolated
//! instances. Platform information comes from the declared Rust compilers.
//!
//! The explicit [`super::verify_resolution`] API invokes this validation.
//! Normal `gnrt sync` does not run the oracle.
//!
//! Requests with GN-conditional features or rustflags, and recipes with
//! conditional dependency removals, skip comparison because they require GN
//! evaluation; dedicated fixtures cover those cases. Unavailable target
//! specifications are skipped with a diagnostic. Validation fails if no
//! platform can be compared.

use crate::collect::{CrateDeclaration, Declaration, DeclarationGroups, Isolation};
use crate::config::BuildConfig;
use crate::package::{ConditionAtom, ResolutionContext, SymbolicCondition};
use crate::sync_context::CrateInfo;
use crate::util::rustc_command;
use anyhow::{bail, ensure, Context, Result};
use guppy::graph::cargo::{CargoOptions, CargoResolverVersion, CargoSet, InitialsPlatform};
use guppy::graph::feature::FeatureId;
use guppy::graph::{
    DependencyDirection, PackageGraph, PackageLink, PackageMetadata, PackageQuery, PackageResolver,
};
use guppy::platform::{EnabledTernary, PlatformSpec};
use guppy::DependencyKind;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use target_spec::{Platform, TargetFeatures};

struct ConcretePlatform {
    platform: Platform,
    cfgs: Vec<cargo_platform::Cfg>,
}

type Node = (String, ResolutionContext);
type Edge = (Node, Node, String, bool);

#[derive(Debug, Default, PartialEq, Eq)]
struct Snapshot {
    features: BTreeMap<Node, BTreeSet<String>>,
    edges: BTreeSet<Edge>,
}

/// Checks unconditional shared requests and each independently isolated closure.
/// GN expressions require GN evaluation before a concrete comparison.
pub(super) fn validate(
    graph: &PackageGraph,
    declarations: &DeclarationGroups,
    crates: &BTreeMap<String, CrateInfo>,
    config: &BuildConfig,
) -> Result<()> {
    let requests: Vec<_> = declarations
        .cargo
        .iter()
        .filter_map(|item| match item {
            Declaration::Crate(declaration) => Some(declaration),
            _ => None,
        })
        .collect();
    if requests.is_empty() {
        return Ok(());
    }
    if requests.iter().any(|declaration| {
        declaration
            .features
            .iter()
            .chain(&declaration.rustflags)
            .any(|value| value.condition().is_some())
    }) {
        log::info!("CargoSet comparison skipped: GN-conditional requests require GN evaluation; concrete comparisons are covered by fixtures");
        return Ok(());
    }
    if crates.values().any(|info| {
        info.package
            .dependencies
            .iter()
            .chain(&info.package.build_dependencies)
            .any(|edge| edge.removal.is_some())
    }) {
        log::info!("CargoSet comparison skipped: conditional dependency removals require a domain-aware policy oracle");
        return Ok(());
    }
    let toolchains: Vec<_> = declarations
        .gn
        .iter()
        .chain(&declarations.cargo)
        .filter_map(|item| match item {
            Declaration::Toolchain(toolchain) => Some(toolchain),
            _ => None,
        })
        .collect();
    let host_toolchain = toolchains
        .iter()
        .find(|toolchain| toolchain.role == "host")
        .copied();
    let compiler = host_toolchain
        .map(|toolchain| toolchain.rustc.as_str())
        .or_else(|| toolchains.first().map(|toolchain| toolchain.rustc.as_str()))
        .unwrap_or("rustc");
    let version = compiler_output(compiler, &["-vV"])?;
    let host_triple = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .context("rustc -vV did not report a host triple")?;
    let Some(host) = concrete_platform(compiler, host_triple)? else {
        bail!("host platform {host_triple} has no comparable target specification");
    };
    let targets: Vec<_> = toolchains
        .iter()
        .filter(|toolchain| toolchain.role != "host")
        .copied()
        .collect();
    let mut verified = 0;
    let mut skipped = 0;
    if targets.is_empty() {
        validate_platform(graph, &requests, crates, &host, &host, config)?;
        verified += 1;
    } else {
        for target in targets {
            match concrete_platform(&target.rustc, &target.target_triple) {
                Ok(Some(platform)) => {
                    validate_platform(graph, &requests, crates, &host, &platform, config)
                        .with_context(|| format!("CargoSet comparison for {}", target.label))?;
                    verified += 1;
                }
                Ok(None) => skipped += 1,
                Err(error) => {
                    return Err(error)
                        .with_context(|| format!("querying toolchain {}", target.label));
                }
            }
        }
    }
    if skipped > 0 {
        log::warn!(
            "CargoSet comparison covered {verified} toolchain(s); \
             {skipped} had an unavailable target specification"
        );
    }
    ensure!(verified > 0, "no toolchain platform could be compared");
    Ok(())
}

fn compiler_output(compiler: &str, query: &[&str]) -> Result<String> {
    let output = rustc_command(compiler)?
        .args(query)
        .output()
        .with_context(|| format!("querying Rust compiler {compiler}"))?;
    ensure!(
        output.status.success(),
        "Rust compiler query failed: {compiler} {query:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).context("Rust compiler query returned non-UTF-8 output")
}

/// Builds the concrete platform for `triple` from the compiler's own output.
///
/// Returns `None` when `triple` is not a builtin target and the compiler
/// cannot print its custom specification (stable toolchains reject the
/// required `-Z` option); callers skip comparison for such toolchains.
fn concrete_platform(compiler: &str, triple: &str) -> Result<Option<ConcretePlatform>> {
    let output = compiler_output(compiler, &["--print", "cfg", "--target", triple])?;
    let cfgs: Vec<cargo_platform::Cfg> = output
        .lines()
        .map(|line| line.parse())
        .collect::<std::result::Result<_, _>>()?;
    let features = TargetFeatures::features(cfgs.iter().filter_map(|cfg| match cfg {
        cargo_platform::Cfg::KeyPair(key, value) if key == "target_feature" => Some(value.clone()),
        _ => None,
    }));
    // Unknown triples must use their actual compiler specification, never a guess.
    let mut platform = match Platform::new_strict(triple.to_owned(), features.clone()) {
        Ok(platform) => platform,
        Err(_) => {
            let json = match compiler_output(
                compiler,
                &[
                    "-Z",
                    "unstable-options",
                    "--print",
                    "target-spec-json",
                    "--target",
                    triple,
                ],
            ) {
                Ok(json) => json,
                Err(error) => {
                    log::warn!(
                        "custom target specification for {triple} is unavailable: {error:#}"
                    );
                    return Ok(None);
                }
            };
            Platform::new_custom(triple.to_owned(), &json, features)?
        }
    };
    platform.add_flags(cfgs.iter().filter_map(|cfg| match cfg {
        cargo_platform::Cfg::Name(name) => Some(name.to_string()),
        _ => None,
    }));
    Ok(Some(ConcretePlatform { platform, cfgs }))
}

fn validate_platform(
    graph: &PackageGraph,
    requests: &[&CrateDeclaration],
    crates: &BTreeMap<String, CrateInfo>,
    host: &ConcretePlatform,
    target: &ConcretePlatform,
    config: &BuildConfig,
) -> Result<()> {
    verify_selectors(graph, host)?;
    verify_selectors(graph, target)?;
    compare_shared(graph, requests, crates, host, target, config)?;
    for declaration in requests
        .iter()
        .filter(|declaration| declaration.isolation == Isolation::Closure)
    {
        compare_scope(
            graph,
            &[*declaration],
            crates,
            &declaration.label,
            host,
            target,
            config,
        )?;
    }
    Ok(())
}

fn verify_selectors(graph: &PackageGraph, platform: &ConcretePlatform) -> Result<()> {
    for package in graph.packages() {
        for link in package.direct_links() {
            for kind in [DependencyKind::Normal, DependencyKind::Build] {
                let status = link.req_for_kind(kind).status();
                for status in [status.required_status(), status.optional_status()] {
                    if let guppy::platform::PlatformStatus::PlatformDependent { eval } = status {
                        for selector in eval.target_specs() {
                            let raw = super::selector_string(selector);
                            let expected: cargo_platform::Platform = raw.parse()?;
                            let actual = selector.eval(&platform.platform);
                            ensure!(actual == Some(expected.matches(platform.platform.triple_str(), &platform.cfgs)),
                                "platform metadata cannot represent selector {raw} for {} (Guppy returned {actual:?})", platform.platform.triple_str());
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn actual_root<'g>(
    graph: &'g PackageGraph,
    declaration: &CrateDeclaration,
) -> Result<PackageMetadata<'g>> {
    let member = super::instance_directory(&declaration.label, &declaration.version);
    let synthetic = graph
        .packages()
        .find(|package| {
            package.in_workspace() && package.name() == super::package_name_for(&member)
        })
        .with_context(|| format!("synthetic root for {} missing", declaration.label))?;
    synthetic
        .direct_links()
        .find(|link| link.to().name() == declaration.package)
        .map(|link| link.to())
        .with_context(|| format!("actual root for {} missing", declaration.label))
}

fn options(host: &ConcretePlatform, target: &ConcretePlatform) -> CargoOptions<'static> {
    let mut options = CargoOptions::new();
    options
        .set_resolver(CargoResolverVersion::V2)
        .set_host_platform(PlatformSpec::Platform(Arc::new(host.platform.clone())))
        .set_target_platform(PlatformSpec::Platform(Arc::new(target.platform.clone())));
    options
}

fn compare_shared(
    graph: &PackageGraph,
    requests: &[&CrateDeclaration],
    crates: &BTreeMap<String, CrateInfo>,
    host: &ConcretePlatform,
    target: &ConcretePlatform,
    config: &BuildConfig,
) -> Result<()> {
    let mut target_seeds = Vec::new();
    let mut host_seeds = Vec::new();
    let options = options(host, target);
    for declaration in requests
        .iter()
        .filter(|request| request.isolation != Isolation::Closure)
    {
        let package = actual_root(graph, declaration)?;
        let mut seeds = vec![FeatureId::base(package.id())];
        if declaration.default_features
            && package.named_features().any(|feature| feature == "default")
        {
            seeds.push(FeatureId::named(package.id(), "default"));
        }
        for feature in declaration.features.iter().flat_map(|entry| entry.values()) {
            seeds.push(FeatureId::named(package.id(), feature));
        }
        if declaration.isolation == Isolation::None {
            host_seeds.extend(seeds.iter().copied());
            if !package.is_proc_macro() {
                target_seeds.extend(seeds);
            }
            continue;
        }
        for context in [ResolutionContext::Target, ResolutionContext::Host] {
            if context == ResolutionContext::Target && package.is_proc_macro() {
                continue;
            }
            let root = (package.id().repr().to_owned(), context);
            let mut root_options = options.clone();
            if context == ResolutionContext::Host {
                root_options.set_initials_platform(InitialsPlatform::Host);
            }
            let reference = CargoSet::with_package_resolver(
                graph.feature_graph().resolve_ids(seeds.iter().copied())?,
                graph.feature_graph().resolve_none(),
                Policy { config },
                &root_options,
            )?;
            let mut expected = cargo_snapshot(&reference, host);
            expected.features.retain(|node, _| node == &root);
            expected.edges.retain(|(from, _, _, _)| from == &root);
            let actual = recipe_snapshot(
                crates,
                &declaration.label,
                vec![root.clone()],
                host,
                target,
                true,
            )?;
            ensure!(
                actual == expected,
                "CargoSet root mismatch for {} ({context:?}): expected {expected:#?}; generated {actual:#?}",
                declaration.label
            );
            // Resolve isolated roots before unifying their outgoing closures.
            target_seeds.extend(
                reference
                    .target_features()
                    .feature_ids(DependencyDirection::Forward)
                    .filter(|feature| {
                        !(context == ResolutionContext::Target
                            && feature.package_id() == package.id())
                    }),
            );
            host_seeds.extend(
                reference
                    .host_features()
                    .feature_ids(DependencyDirection::Forward)
                    .filter(|feature| {
                        !(context == ResolutionContext::Host
                            && feature.package_id() == package.id())
                    }),
            );
        }
    }
    if target_seeds.is_empty() && host_seeds.is_empty() {
        return Ok(());
    }
    let mut pending: Vec<_> = target_seeds
        .iter()
        .map(|feature| {
            (
                feature.package_id().repr().to_owned(),
                ResolutionContext::Target,
            )
        })
        .chain(host_seeds.iter().map(|feature| {
            (
                feature.package_id().repr().to_owned(),
                ResolutionContext::Host,
            )
        }))
        .collect();
    pending.sort();
    pending.dedup();
    let expected = reference_snapshot(graph, target_seeds, host_seeds, host, target, config)?;
    let actual = recipe_snapshot(crates, "shared", pending, host, target, false)?;
    ensure!(
        actual == expected,
        "CargoSet shared mismatch for {}: expected {expected:#?}; generated {actual:#?}",
        target.platform.triple_str()
    );
    Ok(())
}

fn reference_snapshot<'g>(
    graph: &'g PackageGraph,
    target_seeds: Vec<FeatureId<'g>>,
    mut host_seeds: Vec<FeatureId<'g>>,
    host: &ConcretePlatform,
    target: &ConcretePlatform,
    config: &BuildConfig,
) -> Result<Snapshot> {
    let options = options(host, target);
    let target_reference = CargoSet::with_package_resolver(
        graph.feature_graph().resolve_ids(target_seeds)?,
        graph.feature_graph().resolve_none(),
        Policy { config },
        &options,
    )?;
    host_seeds.extend(
        target_reference
            .host_features()
            .feature_ids(DependencyDirection::Forward),
    );
    let mut host_options = options.clone();
    host_options.set_initials_platform(InitialsPlatform::Host);
    let host_reference = CargoSet::with_package_resolver(
        graph.feature_graph().resolve_ids(host_seeds)?,
        graph.feature_graph().resolve_none(),
        Policy { config },
        &host_options,
    )?;
    let mut expected = cargo_snapshot(&target_reference, host);
    expected
        .features
        .retain(|(_, domain), _| *domain == ResolutionContext::Target);
    expected
        .edges
        .retain(|(from, _, _, _)| from.1 == ResolutionContext::Target);
    let host_snapshot = cargo_snapshot(&host_reference, host);
    expected.features.extend(host_snapshot.features);
    expected.edges.extend(host_snapshot.edges);
    Ok(expected)
}

fn compare_scope(
    graph: &PackageGraph,
    requests: &[&CrateDeclaration],
    crates: &BTreeMap<String, CrateInfo>,
    scope: &str,
    host: &ConcretePlatform,
    target: &ConcretePlatform,
    config: &BuildConfig,
) -> Result<()> {
    let mut target_seeds = Vec::new();
    let mut host_seeds = Vec::new();
    let mut roots = Vec::new();
    for declaration in requests {
        let package = actual_root(graph, declaration)?;
        let mut seeds = vec![FeatureId::base(package.id())];
        if declaration.default_features && package.named_features().any(|name| name == "default") {
            seeds.push(FeatureId::named(package.id(), "default"));
        }
        for feature in declaration.features.iter().flat_map(|value| value.values()) {
            seeds.push(FeatureId::named(package.id(), feature));
        }
        host_seeds.extend(seeds.iter().copied());
        roots.push((package.id().repr().to_owned(), ResolutionContext::Host));
        if !package.is_proc_macro() {
            target_seeds.extend(seeds);
            roots.push((package.id().repr().to_owned(), ResolutionContext::Target));
        }
    }
    let expected = reference_snapshot(graph, target_seeds, host_seeds, host, target, config)?;
    let actual = recipe_snapshot(crates, scope, roots, host, target, false)?;
    ensure!(
        actual == expected,
        "CargoSet mismatch in {scope}, target {}: expected {expected:#?}; generated {actual:#?}",
        target.platform.triple_str()
    );
    Ok(())
}

struct Policy<'a> {
    config: &'a BuildConfig,
}

impl<'g> PackageResolver<'g> for Policy<'_> {
    fn accept(&mut self, _query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        super::accept_dependency(&link, self.config)
    }
}

fn cargo_snapshot(cargo: &CargoSet<'_>, host: &ConcretePlatform) -> Snapshot {
    let mut snapshot = Snapshot::default();
    for (domain, features) in [
        (ResolutionContext::Target, cargo.target_features()),
        (ResolutionContext::Host, cargo.host_features()),
    ] {
        for features in features.packages_with_features(DependencyDirection::Forward) {
            snapshot.features.insert(
                (features.package().id().repr().to_owned(), domain),
                features.named_features().map(str::to_owned).collect(),
            );
        }
    }
    for (from_domain, to_domain, build, links) in [
        (
            ResolutionContext::Target,
            ResolutionContext::Target,
            false,
            cargo.target_links().collect::<Vec<_>>(),
        ),
        (
            ResolutionContext::Target,
            ResolutionContext::Host,
            false,
            cargo.proc_macro_links().collect(),
        ),
        (
            ResolutionContext::Target,
            ResolutionContext::Host,
            true,
            cargo.build_dep_links().collect(),
        ),
        (
            ResolutionContext::Host,
            ResolutionContext::Host,
            false,
            cargo.host_links().collect(),
        ),
    ] {
        for link in links {
            let kinds: &[bool] = if from_domain == ResolutionContext::Host {
                &[false, true]
            } else {
                std::slice::from_ref(&build)
            };
            for &build in kinds {
                if from_domain == ResolutionContext::Host {
                    let status = link
                        .req_for_kind(if build {
                            DependencyKind::Build
                        } else {
                            DependencyKind::Normal
                        })
                        .status();
                    let platform = PlatformSpec::Platform(Arc::new(host.platform.clone()));
                    let optional = cargo
                        .host_features()
                        .contains(FeatureId::optional_dependency(
                            link.from().id(),
                            link.dep_name(),
                        ))
                        .unwrap_or(false);
                    if status.required_status().enabled_on(&platform) != EnabledTernary::Enabled
                        && !(optional
                            && status.optional_status().enabled_on(&platform)
                                == EnabledTernary::Enabled)
                    {
                        continue;
                    }
                }
                snapshot.edges.insert((
                    (link.from().id().repr().to_owned(), from_domain),
                    (link.to().id().repr().to_owned(), to_domain),
                    link.resolved_name().to_owned(),
                    build,
                ));
            }
        }
    }
    snapshot
}

fn recipe_snapshot(
    crates: &BTreeMap<String, CrateInfo>,
    scope: &str,
    mut pending: Vec<Node>,
    host: &ConcretePlatform,
    target: &ConcretePlatform,
    roots_only: bool,
) -> Result<Snapshot> {
    let recipes: BTreeMap<_, _> = crates
        .iter()
        .filter_map(|(key, info)| {
            let instance = if info.context == ResolutionContext::Host {
                format!("{scope}#host")
            } else {
                scope.to_owned()
            };
            if info.instance != instance {
                return None;
            }
            key.split_once('|')
                .map(|(_, package)| ((package.to_owned(), info.context), info))
        })
        .collect();
    let mut snapshot = Snapshot::default();
    while let Some(node) = pending.pop() {
        if snapshot.features.contains_key(&node) {
            continue;
        }
        let info = recipes
            .get(&node)
            .with_context(|| format!("missing recipe for {node:?} in {scope}"))?;
        let features = if node.1 == ResolutionContext::Host {
            &info.package.host_features
        } else {
            &info.package.target_features
        };
        let mut enabled = BTreeSet::new();
        for group in features {
            if condition_enabled(&group.condition, host, target)? {
                enabled.extend(group.features.iter().cloned());
            }
        }
        snapshot.features.insert(node.clone(), enabled);
        for (edge, build) in info
            .package
            .dependencies
            .iter()
            .map(|edge| (edge, false))
            .chain(
                info.package
                    .build_dependencies
                    .iter()
                    .map(|edge| (edge, true)),
            )
        {
            let condition = if node.1 == ResolutionContext::Host {
                &edge.host_condition
            } else {
                &edge.target_condition
            };
            if !condition_enabled(condition, host, target)? {
                continue;
            }
            ensure!(
                edge.removal.is_none() && edge.condition.is_none(),
                "CargoSet comparison requires unmodified Cargo dependencies"
            );
            let destination_scope = if roots_only { "shared" } else { scope };
            let expected_instance = if edge.context == ResolutionContext::Host {
                format!("{destination_scope}#host")
            } else {
                destination_scope.to_owned()
            };
            ensure!(edge.instance == expected_instance, "dependency {} -> {} binds outside its feature scope: {} instead of {expected_instance}", info.package.package_name, edge.package_name, edge.instance);
            let (destination_key, destination_info) = crates
                .iter()
                .find(|(_, candidate)| {
                    candidate.instance == edge.instance
                        && candidate.package.package_name == edge.package_name
                        && candidate.package.version == edge.version
                })
                .with_context(|| {
                    format!(
                        "missing bound dependency {} -> {} in {}",
                        info.package.package_name, edge.package_name, edge.instance
                    )
                })?;
            let destination = (
                destination_key
                    .split_once('|')
                    .context("recipe key has no package identity")?
                    .1
                    .to_owned(),
                destination_info.context,
            );
            snapshot.edges.insert((
                node.clone(),
                destination.clone(),
                edge.use_name.clone(),
                build,
            ));
            if !roots_only {
                pending.push(destination);
            }
        }
    }
    Ok(snapshot)
}

fn condition_enabled(
    condition: &SymbolicCondition,
    host: &ConcretePlatform,
    target: &ConcretePlatform,
) -> Result<bool> {
    let Some(terms) = condition else {
        return Ok(true);
    };
    for term in terms {
        let mut enabled = true;
        for atom in term {
            match atom {
                ConditionAtom::Gn { expression } => bail!(
                    "GN condition {expression} requires GN evaluation before CargoSet comparison"
                ),
                ConditionAtom::Cargo { selector, context } => {
                    let platform = if *context == ResolutionContext::Host {
                        host
                    } else {
                        target
                    };
                    let selector: cargo_platform::Platform = selector.parse()?;
                    enabled &= selector.matches(platform.platform.triple_str(), &platform.cfgs);
                }
            }
        }
        if enabled {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn platform_queries_use_the_actual_compiler_and_preserve_cfg_flags() {
        let compiler = "rustc --target=ignored --cfg=gnrt_oracle_probe";
        let version = compiler_output(compiler, &["-vV"]).unwrap();
        let triple = version
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .unwrap();
        let platform = concrete_platform(compiler, triple)
            .unwrap()
            .expect("host triple is builtin");
        assert_eq!(platform.platform.triple_str(), triple);
        assert!(platform
            .cfgs
            .contains(&"gnrt_oracle_probe".parse().unwrap()));
        let command = rustc_command("rustc").unwrap();
        assert_ne!(
            std::path::Path::new(command.get_program())
                .file_name()
                .unwrap(),
            "rustup"
        );
        assert!(compiler_output("rustc --gnrt-invalid-option", &["-vV"]).is_err());
    }

    #[test]
    fn cargo_set_checks_shared_root_closure_and_mixed_frontiers() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().canonicalize().unwrap();
        let write_package = |name: &str, manifest: &str| {
            let directory = root.join(name);
            fs::create_dir_all(directory.join("src")).unwrap();
            fs::write(directory.join("src/lib.rs"), "").unwrap();
            fs::write(
                directory.join("Cargo.toml"),
                format!(
                    "[package]\nname={name:?}\nversion=\"1.0.0\"\nedition=\"2021\"\n{manifest}"
                ),
            )
            .unwrap();
        };
        write_package("leaf", "");
        write_package("weak-leaf", "");
        write_package("optional", "[dependencies]\nweak-leaf={path=\"../weak-leaf\",optional=true}\n[features]\nweak=[\"dep:weak-leaf\"]\n");
        write_package("helper", "[dependencies]\nleaf={path=\"../leaf\",optional=true}\n[features]\nx=[]\ny=[\"dep:leaf\"]\nz=[]\nbuild=[]\nmacro=[]\nmacro_build=[]\n");
        write_package("macro", "[lib]\nproc-macro=true\n[dependencies]\nhelper={path=\"../helper\",default-features=false,features=[\"macro\"]}\n[build-dependencies]\nhelper={path=\"../helper\",default-features=false,features=[\"macro_build\"]}\n");
        fs::write(root.join("macro/build.rs"), "fn main() {}\n").unwrap();
        write_package("library", "[dependencies]\noptional={path=\"../optional\",optional=true}\nhelper_alias={package=\"helper\",path=\"../helper\",default-features=false}\nmacro={path=\"../macro\"}\n[build-dependencies]\nhelper_alias={package=\"helper\",path=\"../helper\",default-features=false,features=[\"build\"]}\n[features]\na=[\"helper_alias/x\",\"optional?/weak\"]\nb=[\"helper_alias/y\",\"dep:optional\"]\n");
        fs::write(root.join("library/build.rs"), "fn main() {}\n").unwrap();
        let mut declarations = DeclarationGroups::default();
        let mut members = Vec::new();
        for (label, package, feature) in [
            ("a", "library", "a"),
            ("b", "library", "b"),
            ("extra", "helper", "z"),
        ] {
            let declaration: CrateDeclaration = serde_json::from_value(serde_json::json!({
                "origin":"cargo", "label":format!("//test:{label}"), "package":package,
                "version":"=1.0.0", "features":[feature], "default_features":false,
                "git":"", "rev":"", "branch":"", "tag":"", "patches":[]
            }))
            .unwrap();
            let directory =
                super::super::instance_directory(&declaration.label, &declaration.version);
            write_package(&super::super::package_name_for(&directory), "");
            fs::write(root.join(&directory).join("Cargo.toml"), format!("[package]\nname={:?}\nversion=\"0.0.0\"\nedition=\"2021\"\n[dependencies]\n{package}={{path=\"../{package}\",default-features=false,features=[{feature:?}]}}\n", super::super::package_name_for(&directory))).unwrap();
            members.push(directory);
            declarations.cargo.push(Declaration::Crate(declaration));
        }
        fs::write(root.join("Cargo.toml"), format!("[workspace]\nresolver=\"2\"\nmembers={members:?}\nexclude=[\"library\",\"helper\",\"macro\",\"leaf\",\"optional\",\"weak-leaf\"]\n")).unwrap();
        let mut metadata = guppy::MetadataCommand::new();
        metadata.cargo_path(env!("CARGO"));
        metadata.current_dir(&root);
        metadata.other_options(vec!["--offline".to_owned()]);
        let graph = metadata.exec().unwrap().build_graph().unwrap();
        let platform = ConcretePlatform {
            platform: Platform::new_strict("x86_64-unknown-linux-gnu", TargetFeatures::none())
                .unwrap(),
            cfgs: vec![],
        };
        for (a, b) in [
            (Isolation::None, Isolation::None),
            (Isolation::Root, Isolation::Root),
            (Isolation::Closure, Isolation::Closure),
            (Isolation::Root, Isolation::Closure),
        ] {
            let mut declarations = declarations.clone();
            for (index, isolation) in [(0, a), (1, b)] {
                let Declaration::Crate(declaration) = &mut declarations.cargo[index] else {
                    unreachable!()
                };
                declaration.isolation = isolation;
            }
            for remove_leaf in [false, true] {
                let mut config = BuildConfig::default();
                if remove_leaf {
                    config.resolve.remove_crates.insert("leaf".to_owned());
                }
                let crates =
                    super::super::resolve_instances(&graph, &declarations, &root, &config).unwrap();
                let requests = declarations
                    .cargo
                    .iter()
                    .filter_map(|item| match item {
                        Declaration::Crate(declaration) => Some(declaration),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                validate_platform(&graph, &requests, &crates, &platform, &platform, &config)
                    .unwrap();
                let mut corrupted = crates.clone();
                let helper = corrupted
                    .values_mut()
                    .find(|info| {
                        info.package.package_name == "helper"
                            && info.context == ResolutionContext::Target
                    })
                    .unwrap();
                helper.package.target_features.clear();
                assert!(validate_platform(
                    &graph, &requests, &corrupted, &platform, &platform, &config
                )
                .is_err());
                let mut corrupted = crates.clone();
                corrupted
                    .values_mut()
                    .find(|info| info.package.package_name == "macro")
                    .unwrap()
                    .package
                    .build_dependencies
                    .clear();
                assert!(validate_platform(
                    &graph, &requests, &corrupted, &platform, &platform, &config
                )
                .is_err());
            }
        }
    }

    #[test]
    fn condition_evaluation_distinguishes_host_target_and_rejects_gn() {
        let host = ConcretePlatform {
            platform: Platform::new_strict("x86_64-unknown-linux-gnu", TargetFeatures::none())
                .unwrap(),
            cfgs: vec!["target_os=\"linux\"".parse().unwrap()],
        };
        let target = ConcretePlatform {
            platform: Platform::new_strict("x86_64-pc-windows-msvc", TargetFeatures::none())
                .unwrap(),
            cfgs: vec!["target_os=\"windows\"".parse().unwrap()],
        };
        let atom = |context| {
            Some(vec![vec![ConditionAtom::Cargo {
                selector: "cfg(target_os = \"linux\")".to_owned(),
                context,
            }]])
        };
        assert!(condition_enabled(&atom(ResolutionContext::Host), &host, &target).unwrap());
        assert!(!condition_enabled(&atom(ResolutionContext::Target), &host, &target).unwrap());
        assert!(!condition_enabled(&Some(vec![]), &host, &target).unwrap());
        assert!(condition_enabled(&None, &host, &target).unwrap());
        assert!(condition_enabled(
            &Some(vec![vec![ConditionAtom::Gn {
                expression: "chip == \"c3\"".to_owned()
            }]]),
            &host,
            &target
        )
        .is_err());
    }
}

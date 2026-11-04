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

//! Parses Cargo target selectors into structured conditions.
//!
//! Conditions retain Cargo's selector tree and host/target scope until the
//! template's `gn_condition` helper serializes them into project GN fields.

use crate::gn_condition::{self, CfgCondition, ConditionExpr};
use crate::package::{ConditionAtom, ResolutionContext, SymbolicCondition};
use anyhow::{Context, Result};
use cargo_platform::{Cfg, CfgExpr};
use target_spec::TargetSpec;

/// Parses the Cargo selectors declared for a dependency edge.
///
/// The selectors are OR-ed. `None` or an empty list means the edge is
/// unconditional.
///
/// # Errors
///
/// Returns an error if any Cargo target selector is invalid.
pub fn edge_condition(
    condition: &Option<Vec<String>>,
    context: ResolutionContext,
) -> Result<Option<ConditionExpr>> {
    let Some(selectors) = condition else {
        return Ok(None);
    };
    if selectors.is_empty() {
        return Ok(None);
    }
    Ok(Some(gn_condition::any(
        selectors
            .iter()
            .map(|selector| parse_selector(selector, context))
            .collect::<Result<Vec<_>>>()?,
    )))
}

/// Parses the Cargo selectors under which a dependency is removed.
///
/// The returned condition is true where none of the removal selectors match.
///
/// # Errors
///
/// Returns an error if any Cargo target selector is invalid.
pub fn removal_condition(when: &[String], context: ResolutionContext) -> Result<ConditionExpr> {
    let removed = gn_condition::any(
        when.iter()
            .map(|selector| parse_selector(selector, context))
            .collect::<Result<Vec<_>>>()?,
    );
    Ok(gn_condition::not(removed))
}

/// Converts resolved feature conditions while preserving each atom's origin.
///
/// `None` and an empty conjunction mean true; an empty disjunction means false.
///
/// # Errors
///
/// Returns an error if a Cargo atom contains an invalid target selector.
pub fn condition_expr(
    condition: &SymbolicCondition,
    _context: ResolutionContext,
) -> Result<Option<ConditionExpr>> {
    let Some(terms) = condition else {
        return Ok(None);
    };
    let terms = terms
        .iter()
        .map(|term| {
            term.iter()
                .map(|atom| match atom {
                    ConditionAtom::Gn { expression } => Ok(ConditionExpr::Gn {
                        expression: expression.clone(),
                    }),
                    ConditionAtom::Cargo { selector, context } => {
                        parse_selector(selector, *context)
                    }
                })
                .collect::<Result<Vec<_>>>()
                .map(gn_condition::all)
        })
        .collect::<Result<Vec<_>>>()?;
    let condition = gn_condition::any(terms);
    Ok((condition != ConditionExpr::True).then_some(condition))
}

/// Parses one Cargo target selector into a scoped condition tree.
///
/// # Errors
///
/// Returns an error if `selector` is not a valid Cargo target selector.
pub fn parse_selector(selector: &str, context: ResolutionContext) -> Result<ConditionExpr> {
    let spec = TargetSpec::new(selector.to_owned())
        .with_context(|| format!("invalid Cargo target selector {selector:?}"))?;
    match spec {
        TargetSpec::PlainString(triple) => Ok(ConditionExpr::CargoTriple {
            context,
            triple: triple.to_string(),
        }),
        TargetSpec::Expression(expression) => {
            let cfg: CfgExpr = expression
                .expression_str()
                .strip_prefix("cfg(")
                .and_then(|value| value.strip_suffix(')'))
                .unwrap_or(expression.expression_str())
                .parse()
                .with_context(|| format!("invalid cfg expression in selector {selector:?}"))?;
            Ok(ConditionExpr::CargoCfg {
                context,
                expression: parse_cfg(&cfg),
            })
        }
    }
}

/// Converts Cargo's parsed cfg expression into the serializable condition IR.
fn parse_cfg(cfg: &CfgExpr) -> CfgCondition {
    match cfg {
        CfgExpr::Not(item) => CfgCondition::Not {
            item: Box::new(parse_cfg(item)),
        },
        CfgExpr::All(items) => CfgCondition::All {
            items: items.iter().map(parse_cfg).collect(),
        },
        CfgExpr::Any(items) => CfgCondition::Any {
            items: items.iter().map(parse_cfg).collect(),
        },
        CfgExpr::Value(Cfg::Name(name)) => CfgCondition::Name {
            name: name.to_string(),
        },
        CfgExpr::Value(Cfg::KeyPair(key, value)) => CfgCondition::KeyValue {
            key: key.to_string(),
            value: value.to_string(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Returns test bindings that distinguish host and target properties.
    fn target_bindings() -> gn_condition::GnConditionBindings<'static> {
        gn_condition::GnConditionBindings {
            target_triple: "target.triple",
            target_cfgs: "target.cfgs",
            host_triple: "host.triple",
            host_cfgs: "host.cfgs",
        }
    }

    /// Parses and renders a selector with the supplied platform context.
    fn render(selector: &str, context: ResolutionContext) -> String {
        gn_condition::render(
            &parse_selector(selector, context).unwrap(),
            target_bindings(),
        )
    }

    #[test]
    fn bare_triple_keeps_its_context_until_rendering() {
        assert_eq!(
            render("x86_64-pc-windows-msvc", ResolutionContext::Target),
            "target.triple == \"x86_64-pc-windows-msvc\""
        );
        assert_eq!(
            render("x86_64-pc-windows-msvc", ResolutionContext::Host),
            "host.triple == \"x86_64-pc-windows-msvc\""
        );
    }

    #[test]
    fn cfg_conditions_keep_nested_structure() {
        assert_eq!(
            render("cfg(target_arch = \"riscv32\")", ResolutionContext::Target),
            "filter_include(target.cfgs, [\"target_arch=\\\"riscv32\\\"\"]) != []"
        );
        assert_eq!(
            render("cfg(all(unix, not(miri)))", ResolutionContext::Host),
            "(filter_include(host.cfgs, [\"unix\"]) != []) && (!(filter_include(host.cfgs, [\"miri\"]) != []))"
        );
    }

    #[test]
    fn feature_atoms_keep_their_origin_context() {
        let condition = Some(vec![vec![
            ConditionAtom::Gn {
                expression: "product == \"a\"".to_owned(),
            },
            ConditionAtom::Cargo {
                selector: "cfg(unix)".to_owned(),
                context: ResolutionContext::Target,
            },
            ConditionAtom::Cargo {
                selector: "cfg(windows)".to_owned(),
                context: ResolutionContext::Host,
            },
        ]]);
        let expression = condition_expr(&condition, ResolutionContext::Host)
            .unwrap()
            .unwrap();
        assert_eq!(
            gn_condition::render(&expression, target_bindings()),
            "(product == \"a\") && (filter_include(target.cfgs, [\"unix\"]) != []) && (filter_include(host.cfgs, [\"windows\"]) != [])"
        );
    }

    #[test]
    fn selectors_and_removals_preserve_boolean_meaning() {
        let selectors = Some(vec!["cfg(unix)".to_owned(), "cfg(windows)".to_owned()]);
        let edge = edge_condition(&selectors, ResolutionContext::Target)
            .unwrap()
            .unwrap();
        assert_eq!(
            gn_condition::render(&edge, target_bindings()),
            "(filter_include(target.cfgs, [\"unix\"]) != []) || (filter_include(target.cfgs, [\"windows\"]) != [])"
        );
        let removal =
            removal_condition(&["cfg(windows)".to_owned()], ResolutionContext::Host).unwrap();
        assert_eq!(
            gn_condition::render(&removal, target_bindings()),
            "!(filter_include(host.cfgs, [\"windows\"]) != [])"
        );
    }
}

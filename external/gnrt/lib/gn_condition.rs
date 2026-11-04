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

//! Represents Cargo and GN conditions until template rendering.
//!
//! The condition tree keeps platform scope and selector meaning separate from
//! project-specific GN property names. The `gn_condition` Handlebars helper
//! serializes the tree using mappings supplied by the template.

use crate::package::ResolutionContext;
use handlebars::{
    Context, Handlebars, Helper, HelperDef, HelperResult, Output, RenderContext, RenderError,
    RenderErrorReason,
};
use serde::{Deserialize, Serialize};

/// A boolean expression used to gate generated GN values.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ConditionExpr {
    /// A condition that always evaluates to true.
    True,
    /// A condition that always evaluates to false.
    False,
    /// A conjunction of conditions.
    All {
        /// Conditions that must all hold.
        items: Vec<ConditionExpr>,
    },
    /// A disjunction of conditions.
    Any {
        /// Conditions of which at least one must hold.
        items: Vec<ConditionExpr>,
    },
    /// The negation of a condition.
    Not {
        /// Condition whose result is inverted.
        item: Box<ConditionExpr>,
    },
    /// A GN expression already supplied by a declaration.
    Gn {
        /// GN boolean expression.
        expression: String,
    },
    /// A Cargo target triple selector and the platform it describes.
    CargoTriple {
        /// Platform whose target triple is tested.
        context: ResolutionContext,
        /// Cargo target triple.
        triple: String,
    },
    /// A Cargo cfg selector and the platform it describes.
    CargoCfg {
        /// Platform whose cfg values are tested.
        context: ResolutionContext,
        /// Parsed Cargo cfg expression.
        expression: CfgCondition,
    },
}

/// A parsed Cargo `cfg` expression.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CfgCondition {
    /// A cfg flag such as `unix`.
    Name {
        /// Cargo cfg flag.
        name: String,
    },
    /// A cfg key/value pair such as `target_arch = "riscv32"`.
    KeyValue {
        /// Cargo cfg key.
        key: String,
        /// Cargo cfg value.
        value: String,
    },
    /// A conjunction of cfg expressions.
    All {
        /// Cfg expressions that must all hold.
        items: Vec<CfgCondition>,
    },
    /// A disjunction of cfg expressions.
    Any {
        /// Cfg expressions of which at least one must hold.
        items: Vec<CfgCondition>,
    },
    /// The negation of a cfg expression.
    Not {
        /// Cfg expression whose result is inverted.
        item: Box<CfgCondition>,
    },
}

/// GN property names used to evaluate Cargo platform selectors.
#[derive(Clone, Copy, Debug)]
pub struct GnConditionBindings<'a> {
    /// GN property containing the target triple.
    pub target_triple: &'a str,
    /// GN list containing target compiler cfg values.
    pub target_cfgs: &'a str,
    /// GN property containing the host triple.
    pub host_triple: &'a str,
    /// GN list containing host compiler cfg values.
    pub host_cfgs: &'a str,
}

/// Combines conditions with logical conjunction and removes redundant nodes.
pub fn all(items: impl IntoIterator<Item = ConditionExpr>) -> ConditionExpr {
    let mut flattened = Vec::new();
    for item in items {
        match item {
            ConditionExpr::False => return ConditionExpr::False,
            ConditionExpr::True => {}
            ConditionExpr::All { items } => flattened.extend(items),
            item => flattened.push(item),
        }
    }
    match flattened.len() {
        0 => ConditionExpr::True,
        1 => flattened.pop().unwrap(),
        _ => ConditionExpr::All { items: flattened },
    }
}

/// Combines conditions with logical disjunction and removes redundant nodes.
pub fn any(items: impl IntoIterator<Item = ConditionExpr>) -> ConditionExpr {
    let mut flattened = Vec::new();
    for item in items {
        match item {
            ConditionExpr::True => return ConditionExpr::True,
            ConditionExpr::False => {}
            ConditionExpr::Any { items } => flattened.extend(items),
            item => flattened.push(item),
        }
    }
    match flattened.len() {
        0 => ConditionExpr::False,
        1 => flattened.pop().unwrap(),
        _ => ConditionExpr::Any { items: flattened },
    }
}

/// Negates a condition and folds boolean constants.
pub fn not(item: ConditionExpr) -> ConditionExpr {
    match item {
        ConditionExpr::True => ConditionExpr::False,
        ConditionExpr::False => ConditionExpr::True,
        ConditionExpr::Not { item } => *item,
        item => ConditionExpr::Not {
            item: Box::new(item),
        },
    }
}

/// Renders a condition tree as a GN boolean expression.
pub fn render(condition: &ConditionExpr, bindings: GnConditionBindings<'_>) -> String {
    match condition {
        ConditionExpr::True => "true".to_owned(),
        ConditionExpr::False => "false".to_owned(),
        ConditionExpr::All { items } => render_joined(
            items
                .iter()
                .map(|item| format!("({})", render(item, bindings))),
            " && ",
            "true",
        ),
        ConditionExpr::Any { items } => render_joined(
            items
                .iter()
                .map(|item| format!("({})", render(item, bindings))),
            " || ",
            "false",
        ),
        ConditionExpr::Not { item } => format!("!({})", render(item, bindings)),
        ConditionExpr::Gn { expression } => expression.clone(),
        ConditionExpr::CargoTriple { context, triple } => format!(
            "{} == {}",
            triple_property(*context, bindings),
            gn_string(triple)
        ),
        ConditionExpr::CargoCfg {
            context,
            expression,
        } => render_cfg(expression, *context, bindings),
    }
}

/// Renders a parsed Cargo cfg tree with the matching platform bindings.
fn render_cfg(
    condition: &CfgCondition,
    context: ResolutionContext,
    bindings: GnConditionBindings<'_>,
) -> String {
    match condition {
        CfgCondition::Name { name } => cfg_leaf(name, context, bindings),
        CfgCondition::KeyValue { key, value } => {
            cfg_leaf(&format!("{key}=\"{value}\""), context, bindings)
        }
        CfgCondition::All { items } => render_joined(
            items
                .iter()
                .map(|item| format!("({})", render_cfg(item, context, bindings))),
            " && ",
            "true",
        ),
        CfgCondition::Any { items } => render_joined(
            items
                .iter()
                .map(|item| format!("({})", render_cfg(item, context, bindings))),
            " || ",
            "false",
        ),
        CfgCondition::Not { item } => {
            format!("!({})", render_cfg(item, context, bindings))
        }
    }
}

/// Renders one cfg flag or key/value pair as a GN list query.
fn cfg_leaf(
    pattern: &str,
    context: ResolutionContext,
    bindings: GnConditionBindings<'_>,
) -> String {
    format!(
        "filter_include({}, [{}]) != []",
        cfgs_property(context, bindings),
        gn_string(pattern)
    )
}

/// Selects the triple property for `context`.
fn triple_property<'a>(context: ResolutionContext, bindings: GnConditionBindings<'a>) -> &'a str {
    match context {
        ResolutionContext::Target => bindings.target_triple,
        ResolutionContext::Host => bindings.host_triple,
    }
}

/// Selects the cfg list property for `context`.
fn cfgs_property<'a>(context: ResolutionContext, bindings: GnConditionBindings<'a>) -> &'a str {
    match context {
        ResolutionContext::Target => bindings.target_cfgs,
        ResolutionContext::Host => bindings.host_cfgs,
    }
}

/// Joins rendered expressions while preserving the empty-input identity.
fn render_joined(
    items: impl IntoIterator<Item = String>,
    operator: &str,
    identity: &str,
) -> String {
    let mut output = String::new();
    for item in items {
        if !output.is_empty() {
            output.push_str(operator);
        }
        output.push_str(&item);
    }
    if output.is_empty() {
        identity.to_owned()
    } else {
        output
    }
}

/// Escapes a string for a GN double-quoted literal.
fn gn_string(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            _ => output.push(character),
        }
    }
    output.push('"');
    output
}

/// Renders a condition using GN property names supplied by the template.
#[derive(Clone, Copy, Debug)]
pub struct GnConditionHelper;

impl HelperDef for GnConditionHelper {
    fn call<'reg: 'rc, 'rc>(
        &self,
        helper: &Helper<'rc>,
        _: &'reg Handlebars<'reg>,
        _: &'rc Context,
        _: &mut RenderContext<'reg, 'rc>,
        output: &mut dyn Output,
    ) -> HelperResult {
        let value = helper
            .param(0)
            .ok_or_else(|| render_error("gn_condition expects a condition argument"))?
            .value()
            .clone();
        let condition: ConditionExpr = serde_json::from_value(value)
            .map_err(|error| render_error(format!("invalid gn_condition value: {error}")))?;
        let target_triple = required_binding(helper, "target_triple")?;
        let target_cfgs = required_binding(helper, "target_cfgs")?;
        let host_triple = required_binding(helper, "host_triple")?;
        let host_cfgs = required_binding(helper, "host_cfgs")?;
        let bindings = GnConditionBindings {
            target_triple: &target_triple,
            target_cfgs: &target_cfgs,
            host_triple: &host_triple,
            host_cfgs: &host_cfgs,
        };
        output.write(&render(&condition, bindings))?;
        Ok(())
    }
}

/// Returns one non-empty string binding supplied by the template.
fn required_binding(helper: &Helper<'_>, key: &str) -> Result<String, RenderError> {
    helper
        .hash_get(key)
        .and_then(|value| value.value().as_str())
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
        .ok_or_else(|| render_error(format!("gn_condition requires non-empty `{key}`")))
}

/// Creates a template error with a condition-helper diagnostic.
fn render_error(message: impl std::fmt::Display) -> RenderError {
    RenderErrorReason::Other(message.to_string()).into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use handlebars::Handlebars;
    use serde_json::json;

    /// Returns test mappings with distinct host and target values.
    fn bindings() -> GnConditionBindings<'static> {
        GnConditionBindings {
            target_triple: "target.triple",
            target_cfgs: "target.cfgs",
            host_triple: "host.triple",
            host_cfgs: "host.cfgs",
        }
    }

    #[test]
    fn combines_and_folds_boolean_conditions() {
        let condition = all([
            ConditionExpr::True,
            ConditionExpr::Gn {
                expression: "enable_rust".to_owned(),
            },
            any([
                ConditionExpr::False,
                ConditionExpr::Not {
                    item: Box::new(ConditionExpr::Gn {
                        expression: "disabled".to_owned(),
                    }),
                },
            ]),
        ]);
        assert_eq!(
            render(&condition, bindings()),
            "(enable_rust) && (!(disabled))"
        );
        assert_eq!(all([]), ConditionExpr::True);
        assert_eq!(any([]), ConditionExpr::False);
        assert_eq!(not(ConditionExpr::True), ConditionExpr::False);
    }

    #[test]
    fn renders_cargo_conditions_in_their_own_context() {
        let condition = all([
            ConditionExpr::CargoCfg {
                context: ResolutionContext::Target,
                expression: CfgCondition::KeyValue {
                    key: "target_arch".to_owned(),
                    value: "riscv32".to_owned(),
                },
            },
            ConditionExpr::CargoTriple {
                context: ResolutionContext::Host,
                triple: "x86_64-apple-darwin".to_owned(),
            },
        ]);
        assert_eq!(
            render(&condition, bindings()),
            "(filter_include(target.cfgs, [\"target_arch=\\\"riscv32\\\"\"]) != []) && (host.triple == \"x86_64-apple-darwin\")"
        );
    }

    #[test]
    fn renders_template_bindings_through_the_helper() {
        let mut registry = Handlebars::new();
        registry.register_escape_fn(handlebars::no_escape);
        registry.register_helper("gn_condition", Box::new(GnConditionHelper));
        let condition = ConditionExpr::CargoCfg {
            context: ResolutionContext::Host,
            expression: CfgCondition::Name {
                name: "unix".to_owned(),
            },
        };
        let output = registry
            .render_template(
                r#"{{gn_condition cond target_triple="target.triple" target_cfgs="target.cfgs" host_triple="host.triple" host_cfgs="host.cfgs"}}"#,
                &json!({"cond": condition}),
            )
            .unwrap();
        assert_eq!(output, "filter_include(host.cfgs, [\"unix\"]) != []");
    }
}

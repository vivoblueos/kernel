use proc_macro2::Span;
use syn::{Error, Result};

/// The current state of the code block finder.
#[derive(Debug)]
pub struct TextProcState {
    code_block: Option<CodeBlock>,
}

#[derive(Debug)]
struct CodeBlock {
    fence: String,
    captured: Option<CapturedCodeBlock>,
    start: Span,
}

#[derive(Debug)]
struct CapturedCodeBlock {
    content: String,
    params: CodeBlockParams,
}

#[derive(Debug)]
struct CodeBlockParams {
    label: Option<String>,
}

/// The output of `TextProcState::step`.
#[derive(Debug)]
pub enum TextProcOutput {
    /// Output the input fragment (`#[doc = "..."]`) without modification,
    /// preserving its positional information.
    Passthrough,
    /// Output nothing.
    Empty,
    /// Output a new documentation text. The positional association between the
    /// input fragment and `.0` is erased.
    Fragment(String),
}

impl TextProcState {
    pub fn new() -> Self {
        Self { code_block: None }
    }

    pub fn step(&mut self, fragment: &str, span: Span) -> TextProcOutput {
        let mut i = 0;

        let mut new_frag: Option<String> = None;

        // If `new_frag` is `None`, then this flag indicates whether the input
        // fragment is outputed as-is.
        let mut passthrough = match self.code_block {
            Some(CodeBlock {
                captured: Some(_), ..
            }) => false,
            _ => true,
        };

        // Disables "pass-through" mode, preparing `new_frag` for custom
        // generation.
        macro_rules! prepare_nonpassthrough_emission {
            () => {
                if new_frag.is_none() {
                    new_frag = Some(if passthrough {
                        fragment[0..i].to_owned()
                    } else {
                        String::new()
                    });
                }
                passthrough = false;
            };
        }

        /// ```text
        /// ^( *(?:`{3,}|~{3,}))\s*(.*?)\s*$
        /// ```
        fn detect_fence(s: &str) -> Option<(&str, &str)> {
            let bytes = s.as_bytes();
            let fence_len = {
                let indent = bytes.iter().take_while(|&&b| b == b' ').count();
                let fence_ch = *bytes.get(indent)?;
                if !matches!(fence_ch, b'`' | b'~') {
                    return None;
                }
                let fence = bytes[indent..]
                    .iter()
                    .take_while(|&&b| b == fence_ch)
                    .count();
                if fence < 3 {
                    return None;
                }
                indent + fence
            };

            let (fence, rest) = s.split_at(fence_len);

            Some((fence, rest.trim()))
        }

        fn remove_indent<'a>(mut line: &'a str, mut indent: &str) -> &'a str {
            while line.len() > 0
                && indent.len() > 0
                && line.as_bytes()[0] == indent.as_bytes()[0]
                && (indent.as_bytes()[0] == b' ' || indent.as_bytes()[0] == b'\t')
            {
                line = &line[1..];
                indent = &indent[1..];
            }
            line
        }

        loop {
            let next_break = fragment[i..].find('\n');

            let line = &fragment[i..];
            let line = if let Some(next_break) = next_break {
                &line[0..next_break]
            } else {
                line
            };

            let mut close_code_block = false;
            let mut passthrough_line = true;

            if let Some(code_block) = &mut self.code_block {
                if line == code_block.fence {
                    // Reached the end of the code block
                    if let Some(mut captured) = code_block.captured.take() {
                        passthrough_line = false;
                        prepare_nonpassthrough_emission!();

                        // Convert this captured code block to a SVG diagram.
                        captured.content.pop(); // Remove trailing "\n"
                        convert_diagram(
                            &captured.content,
                            new_frag.as_mut().unwrap(),
                            captured.params,
                        );
                    }

                    close_code_block = true;
                } else {
                    if let Some(captured) = &mut code_block.captured {
                        captured.content += remove_indent(line, &code_block.fence);
                        captured.content.push('\n');
                        passthrough_line = false;
                    }
                }
            } else {
                // Detect a code block
                if let Some((fence, language)) = detect_fence(line) {
                    let mut code_block = CodeBlock {
                        fence: fence.to_owned(),
                        captured: None,
                        start: span,
                    };

                    let params: Option<CodeBlockParams> = language
                        .strip_prefix("svgbob")
                        .and_then(|rest| {
                            if rest.is_empty() {
                                Some("") // exactly "svgbob"
                            } else {
                                rest.strip_prefix(",") // `Some` if "svgbob,[...]"
                            }
                        })
                        .map(|params| params.parse().unwrap());

                    if let Some(params) = params {
                        // This is the code blcok we are interested in.
                        // Capture the contents.
                        passthrough_line = false;
                        code_block.captured = Some(CapturedCodeBlock {
                            content: String::new(),
                            params,
                        });
                    }

                    self.code_block = Some(code_block);
                }
            }

            if close_code_block {
                self.code_block = None;
            }

            if passthrough_line {
                if let Some(new_frag) = &mut new_frag {
                    *new_frag += line;
                    if next_break.is_some() {
                        new_frag.push('\n');
                    }
                }
            } else {
                if passthrough {
                    prepare_nonpassthrough_emission!();
                }
            }

            if let Some(next_break) = next_break {
                i += next_break + 1;
            } else {
                break;
            }
        }

        if let Some(new_frag) = new_frag {
            TextProcOutput::Fragment(new_frag)
        } else if passthrough {
            TextProcOutput::Passthrough
        } else {
            TextProcOutput::Empty
        }
    }

    pub fn finalize(self) -> Result<()> {
        if let Some(code_block) = self.code_block {
            if code_block.captured.is_some() {
                return Err(Error::new(code_block.start, "unclosed code block"));
            }
        }
        Ok(())
    }
}

impl std::str::FromStr for CodeBlockParams {
    type Err = std::convert::Infallible;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let mut this = CodeBlockParams { label: None };

        let parts = s.split(",").map(|s| s.trim());
        for part in parts {
            if let Some(label) = part
                .strip_prefix("[")
                .and_then(|part| part.strip_suffix("]"))
            {
                this.label = Some(label.to_owned());
            }
        }

        Ok(this)
    }
}

/// The font used for diagrams.
///
/// The selection made here attempts to approximate the monospace font used by
/// rustdoc's stylesheet. Source Code Pro isn't necessarily available because
/// images can't access the containing page's `@font-face`.
const DIAGRAM_FONT: &str =
    "'Source Code Pro','Andale Mono','Segoe UI Mono','Dejavu Sans Mono','Consolas',monospace";

fn convert_diagram(art: &str, output: &mut String, params: CodeBlockParams) {
    let svg_code = to_svg(art);

    // Output the SVG as an image element
    use std::fmt::Write;
    let svg_base64 = base64::encode(&*svg_code);

    if let Some(label) = params.label {
        writeln!(
            output,
            "\n[{}]: data:image/svg+xml;base64,{}",
            label, svg_base64
        )
        .unwrap();
    } else {
        write!(output, "![](data:image/svg+xml;base64,{})", svg_base64).unwrap();
    }
}

#[cfg(feature = "enable")]
fn to_svg(art: &str) -> String {
    use svgbob::{
        sauron::{html::attributes::AttributeValue, Attribute},
        Node,
    };

    // Convert the diagram to SVG
    let mut settings = svgbob::Settings::default();
    settings.stroke_width = 1.0;
    settings.font_family = DIAGRAM_FONT.to_owned();
    settings.font_size = 13;

    let cb = svgbob::CellBuffer::from(art);
    let (mut node, _, _): (svgbob::Node<()>, _, _) = cb.get_node_with_size(&settings);

    traverse_pre_order_mut(&mut node, &mut |node| {
        match node {
            Node::Element(elem) if elem.tag == "text" => {
                // Fix the horizontal layouting of texts by adding a `textLength` attribute
                // to `<text>` elements.
                let mut width = 0;
                for child in elem.get_children() {
                    if let Node::Leaf(leaf) = child {
                        if leaf.is_text() {
                            width += xml_text_width(leaf.unwrap_text());
                        }
                    }
                }

                let text_len = width as f32 * settings.scale as f32;
                elem.attrs.push(Attribute::new(
                    None,
                    "textLength",
                    AttributeValue::from_value(text_len.into()),
                ));

                return false;
            }
            _ => {}
        }

        true
    });

    // FIXME: Replace with let-else when stabilized
    let elem = if let svgbob::Node::Element(elem) = &mut node {
        elem
    } else {
        unreachable!()
    };

    // Patch the root element (`<svg>`)
    for attr in elem.attrs.iter_mut() {
        match *attr.name() {
            "height" => {
                // Fix the height of the image
                // <https://github.com/ivanceras/svgbob/issues/77>
                let new_height = settings.scale * 2.0 * art.lines().count() as f32;
                *attr = Attribute::new(
                    None,
                    "height",
                    AttributeValue::from_value(new_height.into()),
                );
            }
            _ => {}
        }
    }
    elem.attrs.push(Attribute::new(
        None,
        "style",
        AttributeValue::from_value("transform:translate(0.5px,0.5px)".into()),
    ));

    use svgbob::Render;
    let mut svg_code = String::new();
    node.render(&mut svg_code).unwrap();

    svg_code
}

/// Like [`unicode_width::UnicodeWidthStr`] but handles some entity references
/// (e.g., `&amp;`). Assumes the input is in a valid form of an XML text node.
#[cfg(feature = "enable")]
fn xml_text_width(html_text: &str) -> usize {
    use unicode_width::UnicodeWidthStr;
    html_text
        .split('&')
        .enumerate()
        .map(|(i, mut part)| {
            if i > 0 {
                if let Some(k) = part.find(';') {
                    // "& a m p ;"
                    //  ^ ^^^^^ ^
                    //  │   │   └─ This part is preserved so that this entity is
                    //  │   │      counted as one cell
                    //  │   └─ We remove this part now
                    //  └─ This part is removed by `split`
                    part = &part[k..];
                }
            }
            part.width()
        })
        .sum()
}

#[cfg(feature = "enable")]
fn traverse_pre_order_mut<MSG>(
    node: &mut svgbob::Node<MSG>,
    cb: &mut dyn FnMut(&mut svgbob::Node<MSG>) -> bool,
) {
    if cb(node) {
        if let Some(children) = node.children_mut() {
            for child in children.iter_mut() {
                traverse_pre_order_mut(child, cb);
            }
        }
    }
}

#[cfg(not(feature = "enable"))]
fn to_svg(art: &str) -> String {
    use std::fmt::Write;
    use unicode_width::UnicodeWidthStr;

    let lines = art.lines();
    let cols = lines
        .clone()
        .map(|line| line.width())
        .fold(0, std::cmp::max);
    let rows = lines.clone().count();

    let col_width = 8;
    let width = cols * col_width;
    let height = rows * 16;

    let mut content = String::new();
    for (i, line) in lines.enumerate() {
        let mut x = 0;
        let y = i * 16 + 12;
        let mut last_i = 0;

        // Divide `line` by whitespace so that each text span is positioned
        // precisely at their endpoints
        split_whitespace_indices(line, |span, start_i| {
            x += line[last_i..start_i].width() * col_width;
            last_i = start_i;

            write!(
                content,
                r#"<text x="{}" y="{}" textLength="{}">"#,
                x,
                y,
                span.width() * col_width,
            )
            .unwrap();
            escape_html(span, &mut content);
            content.push_str("</text>");
        });
    }

    fn split_whitespace_indices(mut s: &str, mut f: impl FnMut(&str, usize)) {
        // Skip the the first whitespace characters
        let s_trimmed = s.trim_start();
        let mut offset = s.len() - s_trimmed.len();
        s = s_trimmed;
        while !s.is_empty() {
            // Find the first whitespace character
            let i = s
                .char_indices()
                .find(|(_, c)| c.is_whitespace())
                .map(|(i, _)| i);

            // Emit a span comprised of non-whitespace characters
            {
                let i = i.unwrap_or(s.len());
                let part = &s[..i];
                f(part, offset);
                offset += i;
                s = &s[i..];
            }

            // Skip the subsequent whitespace characters
            let s_trimmed = s.trim_start();
            offset += s.len() - s_trimmed.len();
            s = s_trimmed;
        }
    }

    fn escape_html(mut s: &str, out: &mut String) {
        loop {
            let i = s
                .as_bytes()
                .iter()
                .position(|b| matches!(b, b'<' | b'>' | b'&' | 0));
            out.push_str(&s[..i.unwrap_or(s.len())]);
            if let Some(i) = i {
                out.push_str(match s.as_bytes()[i] {
                    b'<' => "&lt;",
                    b'>' => "&gt;",
                    b'&' => "&amp;",
                    0 => " ",
                    _ => unreachable!(),
                });
                s = &s[i + 1..];
            } else {
                break;
            }
        }
    }

    format!(
        include_str!("minimal_template.svg"),
        font = DIAGRAM_FONT,
        width = width,
        height = height,
        content = content,
    )
}

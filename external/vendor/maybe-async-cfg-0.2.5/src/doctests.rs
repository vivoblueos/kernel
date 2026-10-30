use pulldown_cmark::{Parser, Event, Tag, TagEnd, CodeBlockKind};

fn as_lang_tokens(string: &str) -> impl Iterator<Item = &str> {
    // Pandoc, which Rust once used for generating documentation,
    // expects lang strings to be surrounded by `{}` and for each token
    // to be proceeded by a `.`. Since some of these lang strings are still
    // loose in the wild, we strip a pair of surrounding `{}` from the lang
    // string and a leading `.` from each token.

    let string = string.trim();

    let first = string.chars().next();
    let last = string.chars().last();

    let string = if first == Some('{') && last == Some('}') {
        &string[1..string.len() - 1]
    } else {
        string
    };

    string
        .split(|c| c == ',' || c == ' ' || c == '\t')
        .map(str::trim)
        .map(|token| token.strip_prefix('.').unwrap_or(token))
        .filter(|token| !token.is_empty())
}

fn parse_lang(lang: &str) -> Option<(String, String)> {
    let our_prefix = "only_if(";

    let mut has_our_attr = false;
    let mut key = String::new();
    let mut new_lang = String::new();

    for token in as_lang_tokens(lang) {
        if token.starts_with(our_prefix) && token.ends_with(")") {
            has_our_attr = true;
            key = token[our_prefix.len() .. token.len()-1].to_string();
            continue;
        }

        if !new_lang.is_empty() {
            new_lang.push_str(", ");
        }

        new_lang.push_str(token);
    }

    if has_our_attr {
        Some((key, new_lang))
    } else {
        None
    }
}

fn paste_code(new_lang: &str, code: &str, indent: Option<&str>) -> String {
    let mut res = String::new();

    res.push_str("\n``` ");
    res.push_str(new_lang);
    res.push_str("\n");
    res.push_str(code);
    res.push_str("```");

    if let Some(indent) = indent {
        let mut first = true;
        res = res.lines().map(|s| {
            if first {
                first = false;
                return s.to_string()
            };

            let mut res = String::new();
            res.push('\n');
            res.push_str(indent);
            res.push_str(s);

            res
        }).collect();        
    }

    res
}

fn get_indent_from_content(content: &str) -> Option<String> {
    let content = content.as_bytes();
    let mut len = content.len();

    if !(content[len-1] == b'`' && content[len-2] == b'`' && content[len-3] == b'`') {
        return None;
    }

    len -= 3;

    let mut rres: Vec<u8> = vec![];

    while len >= 1 {
        let b = content[len-1];

        if b.is_ascii_whitespace() && !(b == b'\n' || b == b'\r') {
            rres.push(b);
            len -= 1;
        } else {
            break
        }
    }

    let res: String = rres.into_iter().rev().map(|b| b as char).collect();
    
    Some(res)
}

pub fn process_doctests(doc: &str, processor: impl Fn(&str, &str) -> Option<Option<String>>) -> Option<String> {
    let parser = Parser::new(doc);

    let mut prev_offset = 0usize;
    let mut level = 0usize;
    let mut block_key = String::new();
    let mut block_new_lang = String::new();
    let mut inside_code = false;
    let mut code = String::new();
    let mut has_changes: bool = false;

    let mut new_doc = String::new();

    for (event, ref offset) in parser.into_offset_iter() {
        match event {
            Event::Start(Tag::CodeBlock(ref kind)) => {
                level += 1;

                if level == 1 {
                    match match kind {
                        CodeBlockKind::Fenced(ref lang) => {
                            parse_lang(lang)
                        },
                        CodeBlockKind::Indented => {
                            None
                        }
                    } {
                        Some((key, new_lang)) => {
                            let mut new_start = offset.start;
                            let mut success = false;
                            while prev_offset < new_start {
                                let b = doc.as_bytes()[new_start-1];
                                if !b.is_ascii_whitespace() {
                                    break;
                                }

                                if b == b'\n' {
                                    new_start -= 1;
                                    success = true;
                                    break;
                                }
                                new_start -= 1;
                            }
                            if !success {
                                new_start = offset.start;
                            }

                            new_doc.push_str(&doc[prev_offset..new_start]);
                            prev_offset = new_start;
        
                            block_key = key;
                            block_new_lang = new_lang;
                            code.clear();
                            inside_code = true;
                        },
                        None => {},
                    };
                }
            },
            Event::End(TagEnd::CodeBlock) => {
                if level == 1 && inside_code {
                    let content = &doc[prev_offset..offset.end];
                    prev_offset = offset.end;


                    match processor(block_key.as_str(), code.as_str()) {
                        Some(Some(new_code)) => {
                            let indent = get_indent_from_content(content);
                            let new_code = paste_code(block_new_lang.as_str(), new_code.as_str(), indent.as_ref().map(|s| s.as_str()));
                            new_doc.push_str(new_code.as_str());
                            has_changes = true;
                        },
                        Some(None) => {
                            has_changes = true;
                        },
                        None => {
                            new_doc.push_str(content);
                        }
                    }

                    inside_code = false;
                };
                level -= 1;
            },
            Event::Text(ref text) if inside_code => {
                code.push_str(&text);
            },
            _ => {}
        }
    };

    if has_changes {
        if prev_offset < doc.len() {
            new_doc.push_str(&doc[prev_offset..doc.len()]);
        }

        Some(new_doc)
    } else {
        None
    }
}
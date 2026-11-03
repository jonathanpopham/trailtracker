//! XML parser producing the language-neutral lossless CST, plus the small
//! element-reading API the metadata lowerings use.
//!
//! Strategy: build a real element tree (`Element` nodes with `Attr` children,
//! nested elements, text/CDATA leaves) for well-formed regions; anything that
//! does not close properly is kept exactly as its source tokens inside the
//! nearest open node, with an honest `Diagnostic`. Depth is capped: beyond
//! [`MAX_DEPTH`] the parser stops nesting and consumes tokens flat — lossless
//! either way, and immune to hostile nesting.

use crate::core::cst::{Child, Diagnostic, Node, ParseTree, Token};
use crate::core::span::{ByteSpan, SourceId};
use crate::lang::xml::lexer::{kind as tk, lex};

/// CST node-kind labels.
pub mod node {
    pub const DOCUMENT: &str = "Document";
    pub const ELEMENT: &str = "Element";
    pub const ATTR: &str = "Attr";
    /// An unmatched close tag or other structural leftover; exact tokens kept.
    pub const ERROR_ITEM: &str = "ErrorItem";
}

const MAX_DEPTH: usize = 256;

pub fn parse(path: &str, source: &str) -> ParseTree {
    let toks = lex(source);
    let mut p = XmlParser {
        src: source,
        toks,
        i: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let mut children = Vec::new();
    while p.i < p.toks.len() {
        p.parse_item(&mut children);
    }
    let span = ByteSpan::new(0, source.len());
    ParseTree {
        source_id: SourceId::from_path(path),
        path: path.to_string(),
        source: source.to_string(),
        root: Node::new(node::DOCUMENT, span, children),
        diagnostics: p.diags,
    }
}

struct XmlParser<'s> {
    src: &'s str,
    toks: Vec<Token>,
    i: usize,
    diags: Vec<Diagnostic>,
    depth: usize,
}

impl<'s> XmlParser<'s> {
    fn eat(&mut self, out: &mut Vec<Child>) {
        if let Some(t) = self.toks.get(self.i) {
            out.push(Child::Token(t.clone()));
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.toks.get(self.i)
    }

    fn peek_text(&self, t: &Token) -> &str {
        t.span.text(self.src)
    }

    /// One item at the current position: an element, or any other single token
    /// (trivia, text, PI, doctype…) passed through. An unmatched `</…>` here is
    /// wrapped as an `ErrorItem` with a diagnostic.
    fn parse_item(&mut self, out: &mut Vec<Child>) {
        let Some(t) = self.peek() else { return };
        match t.kind {
            k if k == tk::LT => self.parse_element(out),
            k if k == tk::LT_SLASH => {
                let start_span = t.span;
                let mut kids = Vec::new();
                self.eat(&mut kids); // </
                while let Some(t) = self.peek() {
                    let stop = t.kind == tk::GT;
                    self.eat(&mut kids);
                    if stop {
                        break;
                    }
                }
                let span = span_of(&kids).unwrap_or(start_span);
                out.push(Child::Node(Node::new(node::ERROR_ITEM, span, kids)));
                self.diags.push(Diagnostic {
                    code: "xml/unmatched-close",
                    message: "close tag without a matching open tag".to_string(),
                    span,
                });
            }
            _ => self.eat(out),
        }
    }

    /// `<name attrs…>` … `</name>`, or `<name attrs…/>`. The close tag's tokens
    /// live inside the element node, so the element spans its full extent.
    fn parse_element(&mut self, out: &mut Vec<Child>) {
        let mut kids = Vec::new();
        self.eat(&mut kids); // <
        let name = match self.peek() {
            Some(t) if t.kind == tk::NAME => {
                let n = self.peek_text(t).to_string();
                self.eat(&mut kids);
                n
            }
            _ => String::new(),
        };

        // Attributes + tag-internal trivia until `>` or `/>`.
        let mut self_closing = false;
        loop {
            match self.peek() {
                None => break,
                Some(t) if t.kind == tk::GT => {
                    self.eat(&mut kids);
                    break;
                }
                Some(t) if t.kind == tk::SLASH_GT => {
                    self.eat(&mut kids);
                    self_closing = true;
                    break;
                }
                Some(t) if t.kind == tk::NAME => self.parse_attr(&mut kids),
                _ => self.eat(&mut kids),
            }
        }

        if !self_closing {
            self.depth += 1;
            if self.depth > MAX_DEPTH {
                // Too deep: consume flat until our close tag, without recursing.
                self.consume_until_close(&name, &mut kids);
            } else {
                // Children until `</name`.
                loop {
                    match self.peek() {
                        None => {
                            self.diags.push(Diagnostic {
                                code: "xml/unclosed-element",
                                message: format!("element <{name}> is never closed"),
                                span: span_of(&kids).unwrap_or(ByteSpan::new(0, 0)),
                            });
                            break;
                        }
                        Some(t) if t.kind == tk::LT_SLASH => {
                            // Our close tag, or a mismatched one (still consume it
                            // into this element — lossless — with a diagnostic).
                            let close_name = self
                                .toks
                                .get(self.i + 1)
                                .filter(|t| t.kind == tk::NAME)
                                .map(|t| self.peek_text(t).to_string());
                            if close_name.as_deref() != Some(name.as_str()) {
                                self.diags.push(Diagnostic {
                                    code: "xml/mismatched-close",
                                    message: format!(
                                        "expected </{name}>, found </{}>",
                                        close_name.unwrap_or_default()
                                    ),
                                    span: t.span,
                                });
                            }
                            self.eat(&mut kids); // </
                            while let Some(t) = self.peek() {
                                let stop = t.kind == tk::GT;
                                self.eat(&mut kids);
                                if stop {
                                    break;
                                }
                            }
                            break;
                        }
                        Some(_) => self.parse_item(&mut kids),
                    }
                }
            }
            self.depth -= 1;
        }

        let span = span_of(&kids).unwrap_or(ByteSpan::new(0, 0));
        out.push(Child::Node(Node::new(node::ELEMENT, span, kids)));
    }

    /// `name`, `name="value"` — grouped as an `Attr` node.
    fn parse_attr(&mut self, out: &mut Vec<Child>) {
        let mut kids = Vec::new();
        self.eat(&mut kids); // name
                             // Optional `= "value"` with trivia around either token.
        let mut j = self.i;
        while self.toks.get(j).is_some_and(|t| t.trivia) {
            j += 1;
        }
        if self.toks.get(j).is_some_and(|t| t.kind == tk::EQ) {
            while self.i <= j {
                self.eat(&mut kids);
            }
            while self.toks.get(self.i).is_some_and(|t| t.trivia) {
                self.eat(&mut kids);
            }
            if self.peek().is_some_and(|t| t.kind == tk::STRING) {
                self.eat(&mut kids);
            }
        }
        let span = span_of(&kids).unwrap_or(ByteSpan::new(0, 0));
        out.push(Child::Node(Node::new(node::ATTR, span, kids)));
    }

    /// Flat consumption for beyond-depth-cap regions: tokens go straight into
    /// `kids` until `</name>` (or EOF). No recursion, still lossless.
    fn consume_until_close(&mut self, name: &str, kids: &mut Vec<Child>) {
        while let Some(t) = self.peek() {
            if t.kind == tk::LT_SLASH {
                let matches = self
                    .toks
                    .get(self.i + 1)
                    .filter(|t| t.kind == tk::NAME)
                    .is_some_and(|t| self.peek_text(t) == name);
                if matches {
                    self.eat(kids); // </
                    while let Some(t) = self.peek() {
                        let stop = t.kind == tk::GT;
                        self.eat(kids);
                        if stop {
                            break;
                        }
                    }
                    return;
                }
            }
            self.eat(kids);
        }
        self.diags.push(Diagnostic {
            code: "xml/depth-cap",
            message: format!("element <{name}> exceeded depth cap and is never closed"),
            span: span_of(kids).unwrap_or(ByteSpan::new(0, 0)),
        });
    }
}

fn span_of(children: &[Child]) -> Option<ByteSpan> {
    let start = children.first().map(child_span)?;
    let end = children.last().map(child_span)?;
    Some(ByteSpan::new(start.start as usize, end.end as usize))
}

fn child_span(c: &Child) -> ByteSpan {
    match c {
        Child::Node(n) => n.span,
        Child::Token(t) => t.span,
    }
}

// --- element reading API (used by lowerings) --------------------------------

/// The element's tag name (its first non-trivia `name` token).
pub fn tag_name<'a>(el: &Node, src: &'a str) -> Option<&'a str> {
    el.token(tk::NAME).map(|t| t.span.text(src))
}

/// Direct child elements, in document order.
pub fn child_elements(el: &Node) -> impl Iterator<Item = &Node> {
    el.children_of(node::ELEMENT)
}

/// Direct child elements with a given tag name.
pub fn children_named<'a>(
    el: &'a Node,
    name: &'a str,
    src: &'a str,
) -> impl Iterator<Item = &'a Node> + 'a {
    child_elements(el).filter(move |e| tag_name(e, src) == Some(name))
}

/// First direct child element with a given tag name.
pub fn child_named<'a>(el: &'a Node, name: &str, src: &'a str) -> Option<&'a Node> {
    child_elements(el).find(|e| tag_name(e, src) == Some(name))
}

/// Concatenated direct text + CDATA content of an element, trimmed. CDATA
/// wrappers are stripped. Entity references are left as written (honest: this
/// is a metadata reader, not a full XML processor).
pub fn text_content(el: &Node, src: &str) -> String {
    let mut out = String::new();
    for c in &el.children {
        if let Child::Token(t) = c {
            if t.kind == tk::TEXT {
                out.push_str(t.span.text(src));
            } else if t.kind == tk::CDATA {
                let raw = t.span.text(src);
                let inner = raw
                    .strip_prefix("<![CDATA[")
                    .and_then(|s| s.strip_suffix("]]>"))
                    .unwrap_or(raw);
                out.push_str(inner);
            }
        }
    }
    out.trim().to_string()
}

/// Value of an attribute on the element, quotes stripped.
pub fn attr_value<'a>(el: &Node, name: &str, src: &'a str) -> Option<&'a str> {
    for a in el.children_of(node::ATTR) {
        let Some(n) = a.token(tk::NAME) else { continue };
        if n.span.text(src) != name {
            continue;
        }
        let v = a.token(tk::STRING)?;
        let raw = v.span.text(src);
        return Some(raw.trim_matches(|c| c == '"' || c == '\''));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree(src: &str) -> ParseTree {
        parse("test.xml", src)
    }

    #[test]
    fn lossless_on_wellformed_and_broken_inputs() {
        for src in [
            "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<A><b>x</b>\n  <c attr=\"v\"/></A>\n",
            "<a><b>never closed",
            "</orphan><a/>",
            "<a><b></wrong></a>",
            "just text, no markup",
            "",
        ] {
            assert!(tree(src).is_lossless(), "src: {src:?}");
        }
    }

    #[test]
    fn builds_nested_elements_with_text_and_attrs() {
        let src =
            "<CustomField><fullName>Risk__c</fullName><label a=\"1\">Risk</label></CustomField>";
        let t = tree(src);
        let root_el = t.root.child(node::ELEMENT).expect("root element");
        assert_eq!(tag_name(root_el, src), Some("CustomField"));
        let full = child_named(root_el, "fullName", src).expect("fullName");
        assert_eq!(text_content(full, src), "Risk__c");
        let label = child_named(root_el, "label", src).expect("label");
        assert_eq!(attr_value(label, "a", src), Some("1"));
        assert_eq!(text_content(label, src), "Risk");
    }

    #[test]
    fn cdata_is_text_content() {
        let src = "<f><formula><![CDATA[Amount__c > 5 && ISBLANK(X)]]></formula></f>";
        let t = tree(src);
        let f = t.root.child(node::ELEMENT).unwrap();
        let formula = child_named(f, "formula", src).unwrap();
        assert_eq!(text_content(formula, src), "Amount__c > 5 && ISBLANK(X)");
    }

    #[test]
    fn mismatched_close_is_diagnosed_not_dropped() {
        let t = tree("<a><b></c></a>");
        assert!(t.is_lossless());
        assert!(t
            .diagnostics
            .iter()
            .any(|d| d.code == "xml/mismatched-close"));
    }

    #[test]
    fn unmatched_close_becomes_error_item() {
        let t = tree("</ghost>");
        assert!(t.is_lossless());
        assert!(t
            .diagnostics
            .iter()
            .any(|d| d.code == "xml/unmatched-close"));
        assert!(t.root.child(node::ERROR_ITEM).is_some());
    }

    #[test]
    fn hostile_nesting_hits_depth_cap_and_stays_lossless() {
        let mut src = String::new();
        for _ in 0..600 {
            src.push_str("<d>");
        }
        src.push('x');
        // No close tags at all: worst case.
        let t = tree(&src);
        assert!(t.is_lossless());
    }
}

//! MATLAB front end: lossless lexer + CST parser + lowering, wired to the shared
//! IR through the [`LanguageFrontEnd`] seam.
//!
//! MATLAB is keyword-block delimited (not whitespace-significant): `function`,
//! `classdef`, `properties`/`methods`/`events`/`enumeration`, `if`, `switch`,
//! `for`/`parfor`, `while`, `try`, and `spmd` all open a block closed by `end`;
//! a real newline is an ordinary statement separator (the `...` continuation —
//! folded into trivia by the lexer — is the only way to span physical lines).
//! The lexer stays purely lossless (`%` line comments, nesting `%{ … %}` block
//! comments, `...` continuations, single-quoted char arrays with `''` escapes,
//! double-quoted strings with `""` escapes, the char-vs-transpose `'`,
//! hex/bin/float/imaginary numerals) with a per-iteration progress guard. The
//! parser captures definitions, control structure, imports, and calls precisely
//! while keeping expression bodies as balanced token groups. The lowering maps
//! `function`→`Function`, `classdef`→`Type` (+`EXTENDS`) with `methods`→
//! `Function`/`HAS_METHOD` and `properties`/`events`/`enumeration`→`Constant`,
//! `import`→`IMPORTS`, and call sites→`CALLS` **only** when the callee resolves
//! to a known project function (MATLAB's `()` is shared between calls and array
//! indexing, so — like Fortran — unresolved names are assumed to be indexing and
//! never fabricated into edges).
//!
//! # KNOWN UNRESOLVED PUNT: the `.m` extension collision with Objective-C
//!
//! The `.m` extension is claimed by **both** MATLAB and Objective-C. This front
//! end registers `extensions() == ["m"]` as instructed, but **extension routing
//! alone cannot disambiguate the two languages** — a `.m` file may be either.
//! The pipeline dispatches a file to the first registered front end whose
//! `extensions()` claim its extension (see
//! [`crate::lang::frontend::front_end_for_extension`]), so whichever of MATLAB /
//! Objective-C is registered first would unconditionally win every `.m` file.
//! Resolving this requires a **future content-sniffing layer** (e.g. a cheap
//! heuristic over the first non-trivia tokens: `classdef`/`function … end`/`%`
//! comments and `'`-strings for MATLAB vs `#import`/`@interface`/`@implementation`
//! /`//` comments for Objective-C) sitting in front of the pure extension
//! dispatch. That layer does not exist yet and is explicitly **out of scope**
//! here. Until it lands, do not assume `.m` reliably routes to MATLAB.
//!
//! ## Other honest punts (see the lexer/parser/lower module docs for detail)
//! - Genuinely *nested* functions inside an `end`-terminated parent are flattened
//!   to siblings (the script vs nested end-mode is ambiguous without unbounded
//!   lookahead). Lossless; affects nesting depth only.
//! - A leading `!` shell-escape (`!command`) is lexed as ordinary punctuation,
//!   not consumed to end of line.
//! - Command syntax (`hold on`, `disp hello`) is kept as flat tokens and yields
//!   no `CALLS` edge (no parenthesised argument list to key on).
//! - MATLAB is dynamically typed, so no `USES_TYPE` edges are emitted.
//! - Top-level statements in a *script* file are not attributed call edges (there
//!   is no enclosing function to be the caller) — consistent with Julia.
//! - `import` is lowered only at file / classdef-body scope, not when it appears
//!   *inside* a function body (function-local imports yield no `IMPORTS` edge);
//!   calls inside those bodies are still scanned.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The MATLAB language front end. Zero-sized: all state lives in the parse trees
/// and the lowering pass.
pub struct MatlabFrontEnd;

impl LanguageFrontEnd for MatlabFrontEnd {
    fn name(&self) -> &'static str {
        "matlab"
    }

    fn extensions(&self) -> &'static [&'static str] {
        // NOTE: `.m` is shared with Objective-C — extension routing cannot
        // disambiguate the two. See the module-level docs ("the `.m` extension
        // collision"): a future content-sniffing layer is required.
        &["m"]
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        parser::parse(path, source)
    }

    fn module_path(&self, rel_path: &str) -> Vec<String> {
        module_path_for(rel_path)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        // The whole-project lowering produces a self-contained sub-graph (it needs
        // every file at once for the resolution ladder); merge it into the shared
        // graph the pipeline owns.
        let sub = lower::lower(input.package, &input.files, input.manifest_deps);
        graph.merge(sub);
    }
}

/// Map a repo-relative `.m` path to a dotted scope path. Directory segments
/// contribute, with a leading `+` (package folder) or `@` (class folder) marker
/// stripped — MATLAB's `+pkg/Fn.m` and `@Class/method.m` conventions — and the
/// file stem contributes a final segment. The path is a best-effort scope hint;
/// definition identity also comes from `classdef`/`function` declarations, which
/// the lowering tracks separately.
fn module_path_for(rel: &str) -> Vec<String> {
    let mut parts: Vec<&str> = rel.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file.strip_suffix(".m").unwrap_or(file);
    let mut module: Vec<String> = parts
        .iter()
        .map(|s| s.trim_start_matches(|c| c == '+' || c == '@').to_string())
        .filter(|s| !s.is_empty())
        .collect();
    if !stem.is_empty() {
        module.push(stem.to_string());
    }
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.m"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.m"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("+geom/area.m"), vec!["geom", "area"]);
        assert_eq!(module_path_for("@Circle/area.m"), vec!["Circle", "area"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = MatlabFrontEnd;
        assert_eq!(fe.name(), "matlab");
        assert_eq!(fe.extensions(), &["m"]);
    }

    #[test]
    fn lossless_round_trip_on_representative_snippet() {
        // A representative slice of real MATLAB: line + block comments, a
        // classdef with a superclass, a property, a constructor and a method, an
        // import, control flow (if/for/switch), a single- and double-quoted
        // string, a transpose, a `...` continuation, an anonymous function, and
        // `end` used as an index.
        let src = "\
% Geometry demo
classdef Circle < handle
    %{
    A circle with a radius. Block comment alone on its lines.
    %}
    properties
        radius = 1.0
    end
    methods
        function obj = Circle(r)
            obj.radius = r;
        end
        function a = area(obj)
            a = pi * obj.radius .^ 2;
        end
        function s = describe(obj)
            import matlab.lang.makeValidName
            label = \"circle\";
            tag = 'r=';
            sizes = [1 2 3];
            last = sizes(end);
            total = sizes(1) + ...
                    sizes(2);
            sq = @(x) x .^ 2;
            v = sizes';
            if obj.radius > 10
                kind = 'big';
            else
                kind = 'small';
            end
            for i = 1:numel(sizes)
                total = total + sizes(i);
            end
            switch kind
                case 'big'
                    s = describe_big(obj);
                otherwise
                    s = label;
            end
        end
    end
end

function s = describe_big(obj)
    s = obj.radius;
end
";
        let fe = MatlabFrontEnd;
        let tree = fe.parse("Circle.m", src);
        assert!(
            tree.is_lossless(),
            "the MATLAB front end must reconstruct source byte-for-byte"
        );

        // And the lowering produces a non-trivial, deterministic graph.
        let file = crate::lang::frontend::SourceFile {
            rel_path: "Circle.m".to_string(),
            module_path: module_path_for("Circle.m"),
            source: &tree.source,
            root: &tree.root,
        };
        let input = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file],
        };
        let mut g = Graph::new();
        fe.lower(&input, &mut g);
        assert!(g.node_count() > 0);

        let mut g2 = Graph::new();
        let tree2 = fe.parse("Circle.m", src);
        let file2 = crate::lang::frontend::SourceFile {
            rel_path: "Circle.m".to_string(),
            module_path: module_path_for("Circle.m"),
            source: &tree2.source,
            root: &tree2.root,
        };
        let input2 = LoweredInput {
            package: "demo",
            manifest_deps: &[],
            files: vec![file2],
        };
        fe.lower(&input2, &mut g2);
        assert_eq!(
            g.to_jsonl(),
            g2.to_jsonl(),
            "lowering must be deterministic across runs"
        );
    }
}

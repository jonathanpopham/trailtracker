//! Perl front end: lossless lexer + CST parser + lowering, wired to the shared IR
//! through the [`LanguageFrontEnd`] seam.
//!
//! Perl is the canonical context-sensitive language: the lexer disambiguates regex
//! vs division, sigils vs operators, quote-like operators (`q()`/`qq()`/`qw()`/
//! `m//`/`s///`/`tr///`), and heredocs (`<<"EOF"`) with a single value-position
//! bit, while staying purely lossless — every byte is covered, comments / POD
//! (`=pod`…`=cut`) / trailing `__END__`/`__DATA__` sections are retained as trivia,
//! and anything unclassifiable becomes an `error` token. Blocks are brace-delimited
//! and statements end with `;`, so the parser is a depth-guarded brace/`;` splitter
//! that still descends into every group to find nested named subs. The lowering
//! maps `sub`→`Function`, `package`→`Module` (`type_kind: package`),
//! `use parent`/`use base`→`EXTENDS`, `use`/`require`→`IMPORTS`
//! (+`ExternalDependency`/`DEPENDS_ON`), `use constant`/top-level `our`/`my`→
//! `Constant`, and reuses a deterministic scope ladder for `CALLS`.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Perl language front end. Zero-sized: all state lives in the parse trees and
/// the lowering pass.
pub struct PerlFrontEnd;

impl LanguageFrontEnd for PerlFrontEnd {
    fn name(&self) -> &'static str {
        "perl"
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["pl", "pm", "t"]
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

/// Map a repo-relative Perl path to a scope path. A leading `lib/`, `blib/lib/`, or
/// `t/` source root is stripped (common CPAN / test layouts); the remaining
/// directories plus the file stem become the segments.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel
        .strip_prefix("blib/lib/")
        .or_else(|| rel.strip_prefix("lib/"))
        .unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".pm")
        .or_else(|| file.strip_suffix(".pl"))
        .or_else(|| file.strip_suffix(".t"))
        .unwrap_or(file);
    let mut module: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
    module.push(stem.to_string());
    module
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths() {
        assert_eq!(module_path_for("foo.pl"), vec!["foo"]);
        assert_eq!(module_path_for("a/b/c.pm"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("lib/Pkg/Mod.pm"), vec!["Pkg", "Mod"]);
        assert_eq!(module_path_for("blib/lib/X/Y.pm"), vec!["X", "Y"]);
        assert_eq!(module_path_for("t/basic.t"), vec!["t", "basic"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = PerlFrontEnd;
        assert_eq!(fe.name(), "perl");
        assert_eq!(fe.extensions(), &["pl", "pm", "t"]);
    }

    #[test]
    fn round_trips_through_the_front_end() {
        // Lossless contract exercised end-to-end through the trait's `parse`.
        let fe = PerlFrontEnd;
        let src = "\
#!/usr/bin/perl
use strict;

=head1 NAME
demo
=cut

package Demo;
our $N = 42;

sub run {
    my ($self) = @_;
    my @items = qw(a b c);
    return $self->process(@items) // 0;
}

__END__
trailing data
";
        let tree = fe.parse("demo.pl", src);
        assert!(
            tree.is_lossless(),
            "front-end parse must round-trip the source"
        );
    }
}

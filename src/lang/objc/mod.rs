//! Objective-C front end: lossless lexer + CST parser + lowering, wired to the
//! shared IR through the [`LanguageFrontEnd`] seam.
//!
//! Objective-C is the C language plus an `@`-directive object layer, so this front
//! end is built as a C superset: the [`lexer`] and [`parser`] reuse the C strategy
//! (line-based preprocessor, free-form code, bodies captured as balanced
//! token-tree groups) and add the `@` layer (`@interface`/`@implementation`/
//! `@protocol`, methods, `@property`, `@"…"` strings, message sends `[recv msg:]`).
//! The [`lower`]ing maps, honestly (see the IR Atlas):
//!   - `@interface`/`@implementation` → `Type` (`type_kind: class`) with `EXTENDS`
//!     to the superclass and `IMPLEMENTS` to each adopted protocol;
//!   - `@protocol` → `Type` (`type_kind: protocol`);
//!   - methods (`-`/`+`) → `Function` (selector name, `HAS_METHOD` from the type);
//!   - `@property` → `Constant`;
//!   - C functions/`struct`/`enum`/`typedef`/`#define`/globals exactly as the C
//!     front end does; `#import`/`#include`/`@import` → `IMPORTS`
//!     (+`ExternalDependency`/`DEPENDS_ON` for system/module headers);
//!   - message sends and C calls → `CALLS`, resolved by selector/name.
//!
//! # Extension limitation: `.h` is NOT claimed
//!
//! This front end claims only `m` and `mm`. It deliberately does **not** claim
//! `.h`, even though Objective-C `@interface`/`@protocol` declarations conventionally
//! live in `.h` headers: that extension is already claimed by the C and C++ front
//! ends ([`crate::lang::c`], [`crate::lang::cpp`]), and the registry contract
//! requires extensions to be disjoint across front ends. A `.h` file is therefore
//! parsed by whichever of those front ends is registered first and will not see the
//! `@` object layer. In practice this means: when analyzing an Objective-C project,
//! the rich class/protocol/method graph is recovered from `.m`/`.mm` translation
//! units (which carry the `@implementation` and, frequently, class extensions and
//! categories), while `@interface` declarations that live only in `.h` headers are
//! invisible to this front end. Calls to such header-only methods still resolve via
//! the `@implementation`-side method tables; otherwise they fall through to
//! `external`/`UnresolvedSymbol`, never fabricated.

pub mod lexer;
pub mod lower;
pub mod parser;

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

/// The Objective-C language front end. Zero-sized: all state lives in the parse
/// trees and the lowering pass.
pub struct ObjcFrontEnd;

impl LanguageFrontEnd for ObjcFrontEnd {
    fn name(&self) -> &'static str {
        "objc"
    }

    fn extensions(&self) -> &'static [&'static str] {
        // NB: `.h` is intentionally absent — see the module-level limitation note.
        &["m", "mm"]
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

/// Map a repo-relative Objective-C path to its scope segments: the directory
/// components plus the file stem (without the `.m`/`.mm` extension). A `src/` layout
/// root is stripped if present, matching the C front end's convention.
fn module_path_for(rel: &str) -> Vec<String> {
    let trimmed = rel.strip_prefix("src/").unwrap_or(rel);
    let mut parts: Vec<&str> = trimmed.split('/').collect();
    let file = parts.pop().unwrap_or("");
    let stem = file
        .strip_suffix(".mm")
        .or_else(|| file.strip_suffix(".m"))
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
        assert_eq!(module_path_for("main.m"), vec!["main"]);
        assert_eq!(module_path_for("a/b/c.m"), vec!["a", "b", "c"]);
        assert_eq!(module_path_for("src/ui/View.mm"), vec!["ui", "View"]);
        assert_eq!(module_path_for("App/Model.m"), vec!["App", "Model"]);
    }

    #[test]
    fn front_end_identity() {
        let fe = ObjcFrontEnd;
        assert_eq!(fe.name(), "objc");
        assert_eq!(fe.extensions(), &["m", "mm"]);
        // The `.h` collision guard: this front end must not claim `.h`.
        assert!(!fe.extensions().contains(&"h"));
    }

    /// Lossless round-trip on a representative Objective-C snippet exercising
    /// comments, `@"…"` and plain string/char literals, numbers, `#import`/`#define`
    /// preprocessor lines (including a multi-line `#define`), `@protocol`,
    /// `@interface` with a superclass + protocol list + ivars, `@property`,
    /// instance/class methods, message sends, `@import`, an object literal, and a
    /// plain C function.
    #[test]
    fn parse_round_trips_byte_for_byte() {
        let src = "\
/* trailtracker Objective-C front-end self-test */
#import <Foundation/Foundation.h>
#import \"Greeter.h\"
@import UIKit;

#define APP_TAG @\"app\"
#define SUM(a, b) \\
    ((a) + (b))

@protocol Named <NSObject>
- (NSString *)displayName;
@end

@interface Greeter : NSObject <Named> {
    NSUInteger _count;  // backing ivar
}
@property (nonatomic, copy) NSString *name;
+ (instancetype)greeterWithName:(NSString *)name;
- (void)greet:(NSString *)who loudly:(BOOL)loud;
@end

@implementation Greeter
- (void)greet:(NSString *)who loudly:(BOOL)loud {
    NSArray *parts = @[ @\"hi\", who ];
    NSString *msg = [parts componentsJoinedByString:@\" \"];
    if (loud) {
        msg = [msg uppercaseString];
    }
    NSLog(@\"%@ (%lu)\", msg, (unsigned long)_count);
    _count = SUM(_count, 1);
}
@end

static int bump(int n) {
    return n + 1;
}
";
        let fe = ObjcFrontEnd;
        let tree = fe.parse("Greeter.m", src);
        assert!(
            tree.is_lossless(),
            "Objective-C front end must reconstruct source byte-for-byte"
        );
        let mut rebuilt = String::new();
        tree.root.reconstruct(&tree.source, &mut rebuilt);
        assert_eq!(rebuilt, src);
    }
}

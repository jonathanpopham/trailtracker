//! Salesforce metadata front end: CustomObject / CustomField / Flow /
//! ValidationRule XML → the shared IR, on top of the shared lossless XML layer
//! (`crate::lang::xml`).
//!
//! This is the first front end dispatched by *compound suffix* rather than a
//! final extension (the `claims` override the TT-59 seam exists for): all of
//! its files end in `.xml`, and the discriminator is the `-meta.xml` family.
//! Plain `.xml` files remain unclaimed by the registry.

use crate::graph::Graph;
use crate::lang::frontend::{LanguageFrontEnd, LoweredInput};

pub mod expr;
pub mod formula;
pub mod lower;
pub mod perm;

/// Which metadata format a file carries, decided by its compound suffix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetaKind {
    Object,
    Field,
    Flow,
    ValidationRule,
    /// A `Profile` (`X.profile-meta.xml`): object/field access grants (TT-83).
    Profile,
    /// A `PermissionSet` (`X.permissionset-meta.xml`): same shape as a profile,
    /// applied additively rather than per-user-default (TT-83).
    PermissionSet,
    /// A `Workflow` (`X.workflow-meta.xml`): legacy Workflow Rules, field
    /// updates, and alerts for one SObject (TT-78).
    Workflow,
}

impl MetaKind {
    pub fn of(rel_path: &str) -> Option<MetaKind> {
        let name = rel_path.rsplit('/').next().unwrap_or(rel_path);
        if name.ends_with(".object-meta.xml") {
            Some(MetaKind::Object)
        } else if name.ends_with(".field-meta.xml") {
            Some(MetaKind::Field)
        } else if name.ends_with(".flow-meta.xml") {
            Some(MetaKind::Flow)
        } else if name.ends_with(".validationRule-meta.xml") {
            Some(MetaKind::ValidationRule)
        } else if name.ends_with(".profile-meta.xml") {
            Some(MetaKind::Profile)
        } else if name.ends_with(".permissionset-meta.xml") {
            Some(MetaKind::PermissionSet)
        } else if name.ends_with(".workflow-meta.xml") {
            Some(MetaKind::Workflow)
        } else {
            None
        }
    }
}

/// The Salesforce metadata front end. Zero-sized like every other front end.
pub struct SalesforceFrontEnd;

impl LanguageFrontEnd for SalesforceFrontEnd {
    fn name(&self) -> &'static str {
        "salesforce-metadata"
    }

    /// No simple extensions: dispatch happens entirely through `claims`.
    fn extensions(&self) -> &'static [&'static str] {
        &[]
    }

    fn claims(&self, rel_path: &str) -> bool {
        MetaKind::of(rel_path).is_some()
    }

    fn parse(&self, path: &str, source: &str) -> crate::core::cst::ParseTree {
        crate::lang::xml::parser::parse(path, source)
    }

    fn lower(&self, input: &LoweredInput, graph: &mut Graph) {
        let sub = lower::lower(input.package, &input.files);
        graph.merge(sub);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn claims_exactly_the_meta_family() {
        let fe = SalesforceFrontEnd;
        assert!(fe.claims("objects/Case/Case.object-meta.xml"));
        assert!(fe.claims("objects/Case/fields/X__c.field-meta.xml"));
        assert!(fe.claims("flows/Intake.flow-meta.xml"));
        assert!(fe.claims("objects/Case/validationRules/R.validationRule-meta.xml"));
        assert!(fe.claims("profiles/Admin.profile-meta.xml"));
        assert!(fe.claims("permissionsets/Care_Access.permissionset-meta.xml"));
        assert!(fe.claims("workflows/Case__c.workflow-meta.xml"));
        assert!(!fe.claims("pom.xml"));
        assert!(!fe.claims("data.xml"));
        assert!(!fe.claims("Case.object-meta.xml.bak"));
    }

    #[test]
    fn meta_kind_discriminates() {
        assert_eq!(
            MetaKind::of("a/b/C.object-meta.xml"),
            Some(MetaKind::Object)
        );
        assert_eq!(MetaKind::of("f.flow-meta.xml"), Some(MetaKind::Flow));
        assert_eq!(MetaKind::of("x.xml"), None);
    }
}

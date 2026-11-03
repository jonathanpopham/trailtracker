//! TT-83 permissions: lower Salesforce `Profile` and `PermissionSet` metadata
//! into the shared graph — "who can access what."
//!
//! A `Profile` (`X.profile-meta.xml`) and a `PermissionSet`
//! (`X.permissionset-meta.xml`) have the same access-grant shape, so they share
//! one lowering that differs only in `type_kind`:
//!
//! - the component itself → a [`Type`] node (`type_kind="profile"` /
//!   `"permission_set"`, name = the file stem), declared by its file.
//! - each `<objectPermissions>` (`<object>` + `allowRead/allowCreate/allowEdit/
//!   allowDelete`) → a [`USES_TYPE`] edge from the component to `sobject::<object>`
//!   (`via="permission"`, plus the CRUD flags `read/create/edit/delete`). The
//!   object is `ensure_sobject`-d so the grant always lands on a real node.
//! - each `<fieldPermissions>` (`<field>Obj.Field</field>` + `readable/editable`)
//!   → a [`USES_TYPE`] edge to `sobject_field::<Obj>.<Field>`
//!   (`via="field_permission"`, plus `readable/editable`).
//!
//! Grants with an empty object, or a field permission whose `<field>` is not a
//! dotted `Obj.Field`, are skipped — never fabricated. No new ontology kinds:
//! everything rides existing [`Type`] nodes and [`USES_TYPE`] edges, so existing
//! goldens are undisturbed.
//!
//! [`Type`]: crate::ir::ontology::node::TYPE
//! [`USES_TYPE`]: crate::ir::ontology::edge::USES_TYPE

use crate::core::json::Json;
use crate::graph::Graph;
use crate::ir::ontology::{edge, node as ont};
use crate::lang::frontend::SourceFile;
use crate::lang::salesforce::lower::{component_name, ensure_sobject, file_id, root_element};
use crate::lang::xml::parser::{child_named, children_named, text_content};

pub fn lower_profile(g: &mut Graph, f: &SourceFile<'_>) {
    lower_permission_container(g, f, ".profile-meta.xml", "profile", "profile");
}

pub fn lower_permission_set(g: &mut Graph, f: &SourceFile<'_>) {
    lower_permission_container(
        g,
        f,
        ".permissionset-meta.xml",
        "permission_set",
        "permission_set",
    );
}

/// The `permission_set::` / `profile::` node id for a component.
fn component_id(id_prefix: &str, name: &str) -> String {
    format!("{id_prefix}::{name}")
}

/// Read a boolean-ish child as its literal text, defaulting to `"false"` when
/// the element is absent (Salesforce omits false flags in some serializers).
fn bool_flag(el: &crate::core::cst::Node, name: &str, src: &str) -> String {
    child_named(el, name, src)
        .map(|n| text_content(n, src))
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "false".to_string())
}

fn lower_permission_container(
    g: &mut Graph,
    f: &SourceFile<'_>,
    suffix: &str,
    type_kind: &'static str,
    id_prefix: &str,
) {
    let name = component_name(&f.rel_path, suffix);
    let node_id = component_id(id_prefix, &name);
    let mut props = vec![
        ("type_kind", Json::str(type_kind)),
        ("language", Json::str("salesforce-metadata")),
        ("path", Json::str(f.rel_path.clone())),
    ];
    let Some(root) = root_element(f) else {
        g.upsert_node(node_id.clone(), ont::TYPE, name, props);
        g.add_edge(file_id(f), edge::DECLARES, node_id, vec![]);
        return;
    };
    if let Some(label) = child_named(root, "label", f.source) {
        props.push(("label", Json::str(text_content(label, f.source))));
    }
    g.upsert_node(node_id.clone(), ont::TYPE, name, props);
    g.add_edge(file_id(f), edge::DECLARES, node_id.clone(), vec![]);

    // Object-level CRUD grants.
    for op in children_named(root, "objectPermissions", f.source) {
        let object = child_named(op, "object", f.source)
            .map(|n| text_content(n, f.source))
            .unwrap_or_default();
        if object.is_empty() {
            continue;
        }
        let target = ensure_sobject(g, &object);
        g.add_edge(
            node_id.clone(),
            edge::USES_TYPE,
            target,
            vec![
                ("via", Json::str("permission")),
                ("read", Json::str(bool_flag(op, "allowRead", f.source))),
                ("create", Json::str(bool_flag(op, "allowCreate", f.source))),
                ("edit", Json::str(bool_flag(op, "allowEdit", f.source))),
                ("delete", Json::str(bool_flag(op, "allowDelete", f.source))),
            ],
        );
    }

    // Field-level read/edit grants. `<field>` is a dotted `Obj.Field`.
    for fp in children_named(root, "fieldPermissions", f.source) {
        let dotted = child_named(fp, "field", f.source)
            .map(|n| text_content(n, f.source))
            .unwrap_or_default();
        let Some((obj, field)) = dotted.split_once('.') else {
            continue;
        };
        if obj.is_empty() || field.is_empty() {
            continue;
        }
        ensure_sobject(g, obj);
        g.add_edge(
            node_id.clone(),
            edge::USES_TYPE,
            format!("sobject_field::{obj}.{field}"),
            vec![
                ("via", Json::str("field_permission")),
                ("readable", Json::str(bool_flag(fp, "readable", f.source))),
                ("editable", Json::str(bool_flag(fp, "editable", f.source))),
            ],
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::xml::parser::parse;

    fn lower_one(rel: &'static str, src: &'static str) -> Graph {
        let tree = parse(rel, src);
        let file = SourceFile {
            rel_path: rel.to_string(),
            module_path: Vec::new(),
            source: src,
            root: &tree.root,
        };
        crate::lang::salesforce::lower::lower("org", std::slice::from_ref(&file))
    }

    const PROFILE: &str = "<?xml version=\"1.0\"?>\n<Profile>\
        <objectPermissions>\
          <object>Case__c</object>\
          <allowRead>true</allowRead>\
          <allowCreate>true</allowCreate>\
          <allowEdit>true</allowEdit>\
          <allowDelete>false</allowDelete>\
        </objectPermissions>\
        <fieldPermissions>\
          <field>Case__c.Severity__c</field>\
          <readable>true</readable>\
          <editable>false</editable>\
        </fieldPermissions>\
        </Profile>";

    #[test]
    fn profile_emits_object_permission_edge_with_crud() {
        let g = lower_one(
            "force-app/main/default/profiles/Care_Admin.profile-meta.xml",
            PROFILE,
        );
        let node = g
            .nodes()
            .find(|n| n.id == "profile::Care_Admin")
            .expect("profile node");
        assert_eq!(node.kind, ont::TYPE);
        assert_eq!(
            node.props.get("type_kind").map(|j| j.to_line()),
            Some("\"profile\"".to_string())
        );
        // Object permission → USES_TYPE to the shared sobject id, with CRUD.
        let op = g
            .edges()
            .find(|e| {
                e.kind == edge::USES_TYPE
                    && e.from == "profile::Care_Admin"
                    && e.to == "sobject::Case__c"
            })
            .expect("object permission edge");
        assert_eq!(
            op.props.get("via").map(|j| j.to_line()),
            Some("\"permission\"".to_string())
        );
        assert_eq!(
            op.props.get("read").map(|j| j.to_line()),
            Some("\"true\"".to_string())
        );
        assert_eq!(
            op.props.get("create").map(|j| j.to_line()),
            Some("\"true\"".to_string())
        );
        assert_eq!(
            op.props.get("edit").map(|j| j.to_line()),
            Some("\"true\"".to_string())
        );
        assert_eq!(
            op.props.get("delete").map(|j| j.to_line()),
            Some("\"false\"".to_string())
        );
    }

    #[test]
    fn profile_emits_field_permission_edge() {
        let g = lower_one(
            "force-app/main/default/profiles/Care_Admin.profile-meta.xml",
            PROFILE,
        );
        let fp = g
            .edges()
            .find(|e| {
                e.kind == edge::USES_TYPE
                    && e.from == "profile::Care_Admin"
                    && e.to == "sobject_field::Case__c.Severity__c"
            })
            .expect("field permission edge");
        assert_eq!(
            fp.props.get("via").map(|j| j.to_line()),
            Some("\"field_permission\"".to_string())
        );
        assert_eq!(
            fp.props.get("readable").map(|j| j.to_line()),
            Some("\"true\"".to_string())
        );
        assert_eq!(
            fp.props.get("editable").map(|j| j.to_line()),
            Some("\"false\"".to_string())
        );
    }

    #[test]
    fn permission_set_uses_its_own_type_kind() {
        let g = lower_one(
            "force-app/main/default/permissionsets/Care_Access.permissionset-meta.xml",
            "<PermissionSet><objectPermissions><object>Case__c</object>\
             <allowRead>true</allowRead></objectPermissions></PermissionSet>",
        );
        let node = g
            .nodes()
            .find(|n| n.id == "permission_set::Care_Access")
            .expect("permission set node");
        assert_eq!(
            node.props.get("type_kind").map(|j| j.to_line()),
            Some("\"permission_set\"".to_string())
        );
        // Absent CRUD flags default to "false", never fabricated as true.
        let op = g
            .edges()
            .find(|e| e.kind == edge::USES_TYPE && e.from == "permission_set::Care_Access")
            .expect("object permission edge");
        assert_eq!(
            op.props.get("create").map(|j| j.to_line()),
            Some("\"false\"".to_string())
        );
    }
}

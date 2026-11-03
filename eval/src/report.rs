//! Build the verification report as deterministic JSON (reusing the runtime
//! crate's own writer), so it can be hash-attested and diffed across builds.

use trailtracker::core::json::Json;

use crate::property::PropertyOutcome;
use crate::regression::RegressionResult;

/// The whole gate passes iff regression invariants hold and no property failed.
pub fn overall_pass(reg: &RegressionResult, prop: &PropertyOutcome) -> bool {
    reg.passed() && prop.passed()
}

pub fn build(
    reg: &RegressionResult,
    prop: &PropertyOutcome,
    binary_sha256: Option<&str>,
    tool_version: &str,
) -> Json {
    let regression = Json::obj([
        ("passed", Json::Bool(reg.passed())),
        ("files", Json::U64(reg.files as u64)),
        ("lossless_files", Json::U64(reg.lossless_files as u64)),
        ("parse_failures", Json::U64(reg.parse_failures as u64)),
        ("error_bytes", Json::U64(reg.error_bytes as u64)),
        ("nodes", Json::U64(reg.nodes as u64)),
        ("edges", Json::U64(reg.edges as u64)),
        ("deterministic", Json::Bool(reg.deterministic)),
        (
            "violations",
            Json::Array(
                reg.violations
                    .iter()
                    .map(|v| Json::str(v.clone()))
                    .collect(),
            ),
        ),
    ]);

    let failures: Vec<Json> = prop
        .failures
        .iter()
        .map(|f| {
            Json::obj([
                ("seed", Json::U64(f.seed)),
                ("kind", Json::str(f.kind)),
                ("sample", Json::str(f.sample.clone())),
            ])
        })
        .collect();
    let property = Json::obj([
        ("passed", Json::Bool(prop.passed())),
        ("cases", Json::U64(prop.cases as u64)),
        ("failure_count", Json::U64(prop.failures.len() as u64)),
        ("failures", Json::Array(failures)),
    ]);

    Json::obj([
        ("artifact", Json::str("trailtracker-verification-report")),
        ("tool_version", Json::str(tool_version)),
        ("overall_pass", Json::Bool(overall_pass(reg, prop))),
        (
            "binary_sha256",
            match binary_sha256 {
                Some(h) => Json::str(h),
                None => Json::Null,
            },
        ),
        ("regression", regression),
        ("property", property),
    ])
}

//! Config loading — the fixture for the redundant-clone-elim walkthrough.
//! `build` clones `raw` into `owned` and never touches `raw` again: a
//! DATA_DEP-proven last use, so the clone is redundant. `merge` is a decoy —
//! it clones `base` but READS it afterwards, so the rule must refuse it. And
//! `render` is untouched, giving the certificate an unaffected function to
//! re-verify.

/// The redundant clone: `raw` is dead after the copy.
pub fn build(raw: String) -> Settings {
    let raw = raw;
    let owned = raw.clone();
    Settings::parse(owned)
}

/// NOT redundant: `base` is read again after the clone, so eliminating the
/// clone would move out a value the next line still needs.
pub fn merge(base: String) -> (Settings, usize) {
    let base = base;
    let owned = base.clone();
    let s = Settings::parse(owned);
    (s, base.len())
}

/// Untouched by the rewrite; the certificate proves it stayed identical.
pub fn render(s: &Settings) -> String {
    s.to_string()
}

pub struct Settings;
impl Settings {
    pub fn parse(_: String) -> Settings {
        Settings
    }
    pub fn to_string(&self) -> String {
        String::new()
    }
}

//! Order settlement — the fixture for the verified-rewrite walkthrough.
//! Two functions carry recognizable `loop-to-iterator` sites; `audit` is
//! deliberately untouched so the certificate has an unaffected function to
//! re-verify.

pub struct Order {
    pub id: u64,
    pub cents: i64,
    pub valid: bool,
}

/// Sum the settled value of a batch, in cents.
pub fn settled_total(orders: Vec<Order>) -> i64 {
    let mut total = 0;
    for o in orders {
        total += o.cents;
    }
    total
}

/// Collect the ids of the orders that passed validation.
pub fn valid_ids(orders: Vec<Order>) -> Vec<u64> {
    let mut ids = Vec::new();
    for o in orders {
        if o.valid {
            ids.push(o.id);
        }
    }
    ids
}

/// Untouched by the rewrite; the certificate proves it stayed identical.
pub fn audit(ids: &[u64]) -> usize {
    ids.len()
}

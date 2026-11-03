//! Operations: a trait, two implementors, and a stateful engine. Exercises
//! IMPLEMENTS, HAS_METHOD, receiver (`self.`) calls, and qualified calls.

/// A single binary operation.
pub trait Op {
    fn apply(&self, a: i64, b: i64) -> i64;
}

pub struct Add;
pub struct Mul;

impl Op for Add {
    fn apply(&self, a: i64, b: i64) -> i64 {
        a + b
    }
}

impl Op for Mul {
    fn apply(&self, a: i64, b: i64) -> i64 {
        a * b
    }
}

/// Stateful evaluator over a parsed program (a flat list of steps).
pub struct Engine {
    acc: i64,
}

impl Engine {
    /// Qualified-type constructor call site: `Engine::new()`.
    pub fn new() -> Engine {
        Engine { acc: 0 }
    }

    pub fn run(&mut self, program: &[Step]) -> i64 {
        for step in program {
            self.step(step);
        }
        self.acc
    }

    /// Receiver call: `self.combine(...)` resolves against this impl.
    fn step(&mut self, step: &Step) {
        let op = pick(step.op);
        self.acc = self.combine(&op, step.value);
    }

    fn combine(&self, op: &Box<dyn Op>, value: i64) -> i64 {
        op.apply(self.acc, value)
    }
}

impl Default for Engine {
    fn default() -> Engine {
        Engine::new()
    }
}

/// A name that collides with `lib::reset` — global-level ambiguity fuel.
pub fn reset() -> i64 {
    0
}

/// Local helper, resolved within this module.
fn pick(op: OpKind) -> Box<dyn Op> {
    match op {
        OpKind::Add => Box::new(Add),
        OpKind::Mul => Box::new(Mul),
    }
}

#[derive(Clone, Copy)]
pub enum OpKind {
    Add,
    Mul,
}

pub struct Step {
    pub op: OpKind,
    pub value: i64,
}

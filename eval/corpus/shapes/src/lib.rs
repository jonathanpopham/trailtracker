//! A geometry crate: a trait with several implementors whose method names
//! collide (`area`), plus a generic free function. A second fixed corpus repo
//! so the regression harness exercises its multi-repo loop.

pub trait Shape {
    fn area(&self) -> f64;
    fn name(&self) -> &'static str;
}

pub struct Circle {
    pub radius: f64,
}

pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        3.14159 * self.radius * self.radius
    }
    fn name(&self) -> &'static str {
        "circle"
    }
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }
    fn name(&self) -> &'static str {
        "rectangle"
    }
}

/// Generic function: receiver-resolved trait method call on `T`.
pub fn total_area<T: Shape>(shapes: &[T]) -> f64 {
    let mut sum = 0.0;
    for shape in shapes {
        sum += shape.area();
    }
    sum
}

/// Free function calling into the generic above and a constructor.
pub fn describe(radius: f64) -> f64 {
    let circle = Circle { radius };
    total_area(std::slice::from_ref(&circle))
}

//! Modules over the Steenrod algebra, i.e., cohomology rings.

use std::ops::{Add};

use std::collections::HashMap;

use ::steenrod::Square;

/// A free module. The data consist of a set of generators in various
/// degrees, and what each cohomology operation does to those
/// generators.
pub struct Module {
    generators: Vec<usize>,
    // (square, input) -> output
    actions: HashMap<(usize, usize), Vec<usize>>,
}

impl Module {

    /// Create a new module with generators in the given degrees, and no
    /// actions.
    pub fn new(generators: Vec<usize>) -> Module {
        Module {
            generators,
            actions: HashMap::new(),
        }
    }

    /// Add an action to this module, by giving what `Sq^r` for `r = square` does
    /// to the `input`th generator (outputing the sum of the generators in `output`).
    pub fn add_action(&mut self, square: usize, input: usize, output: Vec<usize>) {
        // assert that intput is valid
        assert!(input < self.dimension(), "Generator out of bounds: {}/{}", input, self.dimension());

        // assert that `output` has no repeats, and that they are all valid:
        for i in 0..output.len() {
            assert!(output[i] < self.dimension(), "Generator out of bounds: {}/{}", output[i], self.dimension());
            for j in i + 1..output.len() {
                assert!(i != j, "Repeated generator {} in output of action", i);
            }
        }

        self.actions.insert((square, input), output);
    }

    /// Get the dimension of this module over the Steenrod algebra.
    /// Since this is a free module, it's exactly the number of generators.
    #[inline]
    pub fn dimension(&self) -> usize {
        self.generators.len()
    }

    /// Count the number of generators with degree less than or equal
    /// to a given degree.
    pub fn dimension_at_degree(&self, max: usize) -> usize {
        self.generators.iter().filter(|g| **g <= max).count()
    }

    /// Get the `n`th generator of this module.
    ///
    /// This function will panic of `n >= dimension()`.
    pub fn generator(&self, n: usize) -> Element {
        assert!(n < self.dimension(), "Generator out of bounds: {}/{}", n, self.dimension());
        Element(&self, ElementInner::Single(n))
    }

    /// Get the zero element.
    pub fn zero(&self) -> Element {
        Element(&self, ElementInner::Zero)
    }

    /// Get the degree of the `n`th generator of this module.
    #[inline]
    pub fn degree(&self, n: usize) -> usize {
        self.generators[n]
    }

}

/// An element of a module.
#[derive(Clone)]
pub struct Element<'a>(&'a Module, ElementInner);

#[derive(Clone)]
enum ElementInner {
    Zero,
    Single(usize),
    Alloc(Vec<usize>),
}

impl<'a> Element<'a> {

    fn from_vec(module: &'a Module, xs: Vec<usize>) -> Element {
        Element(module, match xs.len() {
            0 => ElementInner::Zero,
            1 => ElementInner::Single(xs[0]),
            _ => ElementInner::Alloc(xs),
        })
    }

    /// Get the module this element came from.
    #[inline]
    pub fn module(&self) -> &Module {
        &self.0
    }

    /// Whether this element is the zero element.
    pub fn is_zero(&self) -> bool {
        match &self.1 {
            &ElementInner::Zero => true,
            _ => false,
        }
    }

    fn act_one(&self, r: usize) -> Element {
        use self::ElementInner::*;
        match &self.1 {
            &Zero => self.clone(),
            &Single(x) => {
                match self.module().actions.get(&(r, x)) {
                    Some(xs) => Element::from_vec(self.0, xs.clone()),
                    None => Element(self.0, Zero),
                }
            }
            &Alloc(ref xs) => {
                let mut res = self.module().zero();
                for x in xs {
                    match self.module().actions.get(&(r, *x)) {
                        Some(xs) => res = res + Element::from_vec(self.0, xs.clone()),
                        None => {}
                    }
                }
                res
            }
        }
    }

    /// Calculate the action of a Steenrod operation on
    /// this element.
    pub fn act(&self, x: &Square) -> Element {
        let mut total = self.module().zero();
        for sq in x.iter() {
            let mut cur = self.clone();
            for r in sq.iter() {
                /// XXX: this is here because rustc isn't
                /// XXX: smart enough about lifetimes to realize
                /// XXX: that self.0 *always* lives as long as &self
                /// XXX: does, so it's fine to transmute the lifetime
                /// XXX: into the largest one possible. most of the
                /// XXX: problem comes from the fact that the type
                /// XXX: system has no good way of encoding that this
                /// XXX: element depends on a value of type Module
                /// XXX: (i.e., no dependent types).
                use std::mem::transmute;
                cur = unsafe {
                    transmute(cur.act_one(*r))
                }
            }
            total = total + cur;
        }
        total
    }


}

impl<'a, 'b1, 'b2> Add<&'b1 Element<'a>> for &'b2 Element<'a> {
    type Output = Element<'a>;
    fn add(self, that: &'b1 Element<'a>) -> Self::Output {
        use self::ElementInner::*;
        match (&self.1, &that.1) {
            (&Zero, a) => Element(self.0, a.clone()),
            (a, &Zero) => Element(self.0, a.clone()),
            (&Single(x), &Single(y)) =>
                if x == y {
                    Element(self.0, Zero)
                } else {
                    Element(self.0, Alloc(vec![x, y]))
                },
            (&Single(x), &Alloc(ref ys)) => {
                let mut zs = ys.iter().map(|y| *y).filter(|y| *y == x).collect::<Vec<_>>();
                if zs.len() == ys.len() {
                    zs.push(x);
                }
                Element::from_vec(self.0, zs)
            }
            (&Alloc(ref xs), &Single(y)) => {
                let mut zs = xs.iter().map(|x| *x).filter(|x| *x == y).collect::<Vec<_>>();
                if zs.len() == xs.len() {
                    zs.push(y);
                }
                Element::from_vec(self.0, zs)
            }
            (&Alloc(ref xs), &Alloc(ref ys)) => {
                let mut zs = Vec::new();
                for x in xs {
                    if !ys.contains(x) {
                        zs.push(*x);
                    }
                }
                for y in ys {
                    if !xs.contains(y) {
                        zs.push(*y);
                    }
                }
                Element::from_vec(self.0, zs)
            }
        }
    }
}

impl<'a, 'b> Add<&'b Element<'a>> for Element<'a> {
    type Output = Element<'a>;
    fn add(self, that: &'b Element<'a>) -> Self::Output {
        &self + that
    }
}

impl<'a, 'b> Add<Element<'a>> for &'b Element<'a> {
    type Output = Element<'a>;
    fn add(self, that: Element<'a>) -> Self::Output {
        self + &that
    }
}

impl<'a> Add<Element<'a>> for Element<'a> {
    type Output = Element<'a>;
    fn add(self, that: Element<'a>) -> Self::Output {
        &self + &that
    }
}
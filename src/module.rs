//! Modules over the Steenrod algebra, i.e., cohomology rings.

use std::ops::{ Add, AddAssign };

use std::collections::HashMap;

use ::steenrod::Square;

use bit_set::BitSet;

/// A Steenrod module, whose underlying F2 module is free.
///
/// The data consist of a set of generators in various
/// degrees, and what each cohomology operation does to those
/// generators.
pub struct Module {
    generators: Vec<usize>,
    // actions[generator][square] -> output
    actions: Vec<Vec<Element>>,
}

impl Module {

    /// Create a new module with generators in the given degrees, and no
    /// actions.
    pub fn new(generators: Vec<usize>) -> Module {
        Module {
            generators,
            actions: Vec::new(),
        }
    }

    /// Add another generator, and return the number representing it.
    pub fn add_generator(&mut self, degree: usize) -> usize {
        self.generators.push(degree);
        self.actions.push(Vec::new());
        self.generators.len() - 1
    }

    /// Add an action to this module, by giving what `Sq^r` for `r = square` does
    /// to the `input`th generator (outputing the sum of the generators in `output`).
    pub fn add_action(&mut self, square: usize, input: usize, output: Element) {
        // assert that intput is valid
        assert!(input < self.dimension(), "Generator out of bounds: {}/{}", input, self.dimension());

        while self.actions[input].len() <= square {
            self.actions.push(Vec::new());
        }

        self.actions[input][square] = output;
    }

    /// Get the dimension of this module over the Steenrod algebra.
    /// Since this is a free module, it's exactly the number of generators.
    #[inline]
    pub fn dimension(&self) -> usize {
        self.generators.len()
    }

    /// Get the connectivity of this module, i.e., the lowest degree of
    /// any generator.
    #[inline]
    pub fn connectivity(&self) -> usize {
        *self.generators.iter().min().unwrap()
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
        Element::new(&[n])
    }

    /// Get a basis for the whole module.
    pub fn basis(&self) -> Vec<Element> {
        self.iter()
            .map(|(g, _)| Element::new(&[g]))
            .collect::<Vec<_>>()
    }

    /// Get a basis for the given degree of this module.
    pub fn basis_at_degree(&self, degree: usize) -> Vec<Element> {
        self.iter()
            .filter(|&(g, d)| *d == degree)
            .map(|(g, _)| Element::new(&[g]))
            .collect::<Vec<_>>()
    }

    pub fn iter(&self) -> ::std::iter::Enumerate<::std::slice::Iter<usize>> {
        self.generators.iter().enumerate()
    }

    /// Get the zero element.
    #[inline]
    pub fn zero(&self) -> Element {
        Element::new(&[])
    }

    /// Get the degree of the `n`th generator of this module.
    #[inline]
    pub fn degree(&self, n: usize) -> usize {
        self.generators[n]
    }

}

/// An element of `F_2^infty`. These can be be used to
/// simulate elements of a Steenrod module, if supplied
/// with action data.
// Implementation note: it's best to implement these guys
// as packed bit vectors; after all, it's an F2 module!
#[derive(Clone)]
pub struct Element(BitSet);

impl Element {

    /// Create a new module as a sum of given generators
    fn new(generators: &[usize]) -> Element {
        Element(generators.iter().map(|x| *x).collect())
    }

    /// Whether this element is the zero element.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn act_one(&self, m: &Module, r: usize) -> Element {
        let mut res = m.zero();
        for x in &self.0 {
            for y in &m.actions[x][r].0 {
                if res.0.contains(y) {
                    res.0.remove(y);
                } else {
                    res.0.insert(y);
                }
            }
        }
        res.0.shrink_to_fit();
        res
    }

    /// Calculate the action of a Steenrod operation on
    /// this element, given action data.
    pub fn act(&self, m: &Module, x: &Square) -> Element {
        let mut total = m.zero();
        for sq in x.iter() {
            let mut cur = self.clone();
            for r in sq.iter() {
                cur = cur.act_one(m, *r)
            }
            total = total + cur;
        }
        total
    }

    /// Get a reference to the backing bitset.
    pub fn as_ref(&self) -> &BitSet {
        &self.0
    }

    /// Get a mutable reference to the backing bitset.
    pub fn as_mut(&mut self) -> &mut BitSet {
        &mut self.0
    }

    /// Convert this module element into a bitset of generators.
    pub fn into_inner(self) -> BitSet {
        self.0
    }

}

impl<'b1, 'b2> Add<&'b1 Element> for &'b2 Element {
    type Output = Element;
    #[inline]
    fn add(self, that: &'b1 Element) -> Self::Output {
        let mut res = self.clone();
        res += that;
        res
    }
}

impl<'b1> AddAssign<&'b1 Element> for Element {
    #[inline]
    fn add_assign(&mut self, that: &'b1 Element) {
        self.0.symmetric_difference_with(&that.0);
    }
}

vector_add_extra!(Element);
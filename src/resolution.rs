//! Tools for computing free resolutions of a free Steenrod module.

use super::module::{ Module, Element };
use super::steenrod::Milnor;

use std::collections::HashMap;

use bit_set::BitSet;

/// An element of a "higher" Ext group.
struct HigherElement(Vec<Milnor>);

/// A "higher" Ext group. `Ext^0(M, k) = M`, and the
/// higher ones are quotients fo free groups, so it's better
/// to deal with them separately.
struct HigherExt {
    // the degrees of the generators
    generators: Vec<usize>,
    // and their images in the differential
    differentials: Vec<usize, Vec<Milnor>>,
}

trait MaxDegree {
    /// return the highest degree element of
    /// `self`, and its degree. (el, degree)
    fn max_degree(&self) -> (usize);
}

impl<'a> MaxDegree<usize> for (&'a Module, Element) {
    fn max_degree(&self) -> (usize) {
        self.1.as_ref().into_iter().map(|g| self.0.degree(g)).max().unwrap()
    }
}

impl<'a> MaxDegree<Milnor> for (&'a HigherExt, HigherElement) {
    fn max_degree(&self) -> (usize, usize) {
        self.1.as_ref().into_iter().map(|g| self.0.degree(g)).max().unwrap()
    }
}

/// A free resolution of a Steenrod module, for calculating
/// its Ext modules. In particular, we use this data to compute
/// `Ext^(s,t)(M,k)`.
pub struct Resolution {
    // the module M, also the bottom Ext group.
    module: Module,

    // the first Ext group, Ext^1 which has a differential
    // landing in M
    first_ext_generators: Vec<usize>,
    first_ext_differential: Vec<usize, Element>,

    // the rest of the Exts, whose differentials flow into
    // each other. Note that Ext^2 is higher_exts[0].
    higher_exts: Vec<HigherExt>,

    // the first kernel is a submodule of M. first_ker[t] is
    // a basis for the kernel in degree t.
    first_ker: Vec<Vec<Element>>,

    // the rest of the kernels. indices are higher_kers[t][s]
    higher_kers: Vec<Vec<Vec<HigherElement>>>,

    // the first image, which is a submodule of M. consists of
    // pairs (x, dx), with x lying in Ext^1
    first_im: Vec<Vec<(HigherElement, Element)>>,

    // the rest of the images.
    higher_ims: Vec<Vec<Vec<(HigherElement, HigherElement)>>>,

    // the maximum filtration degree calculated for
    // a given internal degree
    max_filtration: fn(usize) -> usize,

    // current internal degree
    t: usize,

    // current filtration
    s: usize,
}

impl Resolution {

    /// Creates a new resolution with the given initial conditions.
    ///
    /// `max_filtration` represents a heuristic bound, i.e., how far
    /// to go on filtration on a given internal degree.
    pub fn new(module: Module, max_filtration: fn(usize) -> usize) -> Resolution {
        unimplemented!()
    }

    fn step_t(&mut self) {
        self.ker.push(Vec::new());
        self.im.push(Vec::new());

        self.ker[self.t].push(vec![self.module.basis_at_degree(self.t).into_iter()
            .map(Element::into_bitset)
            .collect());

        for s in 0 .. (self.max_filtration)(self.t) + 1 {
            self.ker[self.t].push(Vec::new());
            self.im[self.t].push(Vec::new());

            for (g, d) in self.ext[s - 1].iter() {
                for op in Milnor::basis_of_degree(self.t - d) {

                    let x = match self.ext[s] {
                        Ext::Ground(m) => m.generator(g).act(&op.into_sum().to_square())
                    }

                    let x = self.ext[s].generator(g).act(&op.into_sum().to_square()).into_bitset();
                    let mut dx = BitSet::new();
                    for g in &x {
                        dx.symmetric_difference_with(self.ext[s].1.get(&g).unwrap());
                    }
                    self.reduce(s, Some(&mut x), Some(&mut dx));
                    if dx.is_empty() {
                        self.ker[self.t][s + 1].push(x);
                    } else {
                        let highest = dx.iter().last().unwrap();
                        let index = self.im[self.t][s].iter()
                            .rposition(|a| a.1.iter().last().unwrap() == highest)
                            .unwrap_or(0);
                        self.im[self.t][s].insert(index, (x, dx));
                    }
                }
            }

            for mut cyc in self.ker[self.t][s].clone() {
                self.reduce(s, None, Some(&mut cyc));
                if !cyc.is_empty() {
                    if self.ext.len() <= s {
                        self.ext.push((Module::new(vec![]), HashMap::new()));
                    }
                    let num = self.ext[s].0.add_generator(self.t);
                    self.ext[s].1.insert(num, cyc);
                }
            }
        }
    }

    fn reduce<A, B>(im: &Vec<(A, B)>, s: usize, x: Option<&mut A>, dx: &mut B)
        where A: for<'a> AddAssign<&'a A> +

    {
        let im = &self.im[self.t][s];
        fn degree(this: &Resolution, s: usize, x: &BitSet) -> usize {
            x.as_ref().into_iter().map(|g| this.ext[s].degree(g)).max()
        }
        'main: loop {
            let mut changed = false;
            for a in im.iter().rev() {
                if dx.is_empty() {
                    break 'main
                }
                if dx.as_ref().contains(degree(&self, s, &a.1)) {
                    x.map(|x| x += &a.0);
                    dx += &a.1;
                }
            }
            let deg_dx = degree(&self, s, &dx);
            if !im.iter().any(|a| degree(&self, s, a) == dx) {
                break
            }
        }
    }
}
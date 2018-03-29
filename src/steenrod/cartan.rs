//! Steenrod operations, encoded in the Serre-Cartan basis.
//!
//! This basis is useful for efficiently computing actions on modules, and for
//! efficient comparisons, but creating them via the Adem relations is inefficient.
//!
//! Given a sequence of squares `Sq^(i1,...,ik)`, we say that it is *admissible*
//! if `ij < 2i(j+1)` for all `j`. Such sequence of squares form a basis for
//! the Steenrod algebra, the Serre-Cartan basis.

use std::ops::{Add, AddAssign, Mul, Index, IndexMut};

use std::fmt::{Display, Formatter, Result as FResult};

use std::slice::{Iter as VIter};
use std::iter::Rev;

use linked_hash_set::{LinkedHashSet, Iter as LHSIter};

use super::{ Milnor, Square };

/// A basis element of the Steenrod algebra, encoded in the Serre-Cartan basis.
#[derive(Clone, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CartanBasis(
    // important invariant: the sequence given is admissible. Note that
    // the order is as in Sq^(i1,...,ik), so acting on u acts by Sq^ik first.
    //
    // moreover, there are no zeros in this vector, since Sq^0 = 1
    Vec<usize>
);

impl CartanBasis {

    /// An iterator over the squares in this basis element, in order
    /// of application, i.e., iterating on `Sq^(i1,...,ik)` will
    /// return `Sq^ik` first.
    pub fn iter(&self) -> Rev<VIter<usize>> {
        self.0.iter().rev()
    }

    /// Convert this basis element into a Cartan sum.
    pub fn into_sum(self) -> Cartan {
        let mut result = Cartan::zero();
        result.0.insert(self);
        result
    }
}

impl Display for CartanBasis {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        write!(f, "{}", self.0.iter().map(|x| format!("Sq^{}", x)).collect::<Vec<_>>().join(" "))
    }
}

/// An element of the Steenrod algebra, encoded as a sum of
/// admissible products of Steenrod squares, i.e., the
/// Cartan basis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cartan(
    // each element corresponds to a product of
    // Steenrod squares, whose elements are the r in Sq^r
    // we store things in a hash set since it makes addition
    // easier and we're only working mod 2
    LinkedHashSet<CartanBasis>,
);


impl Cartan {

    /// Get the zero element in this basis.
    pub fn zero() -> Cartan {
        Cartan(LinkedHashSet::new())
    }

    /// Create a new element as a sum of Milnor basis elements.
    pub fn sum_of(vec: Vec<Vec<usize>>) -> Cartan {
        let mut res = Cartan::zero();
        for xs in adem::simplify(vec) {
            let op = CartanBasis(xs);
            if !res.0.remove(&op) {
                res.0.insert(op);
            }
        }
        res
    }

    /// An iterator over the summands of this Steenrod element.
    pub fn iter(&self) -> LHSIter<CartanBasis> {
        self.0.iter()
    }

    /// Convert this Steenrod element to the Milnor basis.
    pub fn to_milnor(&self) -> Milnor {
        self.to_square().to_milnor()
    }

    /// Convert this Steenrod element to a sum of squares.
    pub fn to_square(&self) -> Square {
        Square::sum_of(self.iter().map(|sq| sq.0.iter().map(|x| *x).collect::<Vec<_>>()).collect::<Vec<_>>())
    }
}

vector_additon!(Cartan, Cartan, CartanBasis, CartanBasis::clone);

impl Display for Cartan {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        if self.0.is_empty() {
            write!(f, "0")
        } else {
            let mut copy = self.0.iter().map(CartanBasis::clone).collect::<Vec<_>>();
            copy.sort();
            write!(f, "{}", copy.iter()
                .map(|op| format!("{}", op))
                .collect::<Vec<_>>()
                .join(" + "))
        }
    }
}

mod adem {

    //! Functions for Adem simplification.

    /// An iterator over the terms of the Adem relation of two squares.
    ///
    /// ```
    /// Sq^i Sq^j = sum_k^(i/2) binom(j - k - 1, i - 2k) Sq^(i+j-k) Sq^k
    /// ```
    pub struct AdemRel {
        i: usize,
        j: usize,
        k: usize,
    }

    impl AdemRel {
        pub fn new(i: usize, j: usize) -> AdemRel {
            AdemRel { i, j, k: 0 }
        }

        #[inline]
        fn advance(&mut self) -> Option<(usize, usize)> {
            #[inline]
            fn binom(n: usize, k: usize) -> bool {
                n & k == k
            }

            let val = if binom(self.j - self.k - 1, self.i - (self.k << 1)) {
                Some((self.i + self.j - self.k, self.k))
            } else {
                None
            };

            self.k += 1;
            val
        }
    }

    impl Iterator for AdemRel {
        type Item = (usize, usize);
        fn next(&mut self) -> Option<Self::Item> {
            while self.k <= self.i / 2 {
                if let Some(val) = self.advance() {
                    return Some(val)
                }
            }
            None
        }
    }

    pub fn admissible(powers: &Vec<usize>) -> bool {
        for pair in powers[..].windows(2) {
            if pair[0] < 2 * pair[1] {
                return false
            }
        }
        true
    }

    // adapted from https://math.berkeley.edu/~kruckman/adem/adem.rkt

    pub fn simplify(sum: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        if sum.iter().all(admissible) {
            sum
        } else {
            simplify(sum.into_iter()
                .rev()
                .fold(Vec::new(), |mut xs, x| {
                    let mut simple = simplify_prod(&x[..]);
                    for op in &mut simple {
                        op.retain(|x| *x != 0)
                    }
                    xs.extend(simple);
                    xs
                }))
        }

    }

    fn simplify_prod(op: &[usize]) -> Vec<Vec<usize>> {
        if op.len() <= 1 {
            vec![op.into()]
        } else if op[0] >= 2 * op[1] {
            simplify_prod(&op[1..]).into_iter()
                .map(|mut x| { x.insert(0, op[0]); x })
                .collect::<Vec<_>>()
        } else {
            let mut res = Vec::new();
            for (a, b) in AdemRel::new(op[0], op[1]) {
                let mut vec = vec![a, b];
                vec.extend(op[2..].iter().map(|x| *x));
                res.push(vec);
            }
            res
        }
    }
}
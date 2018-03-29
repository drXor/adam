//! Steenrod operations, encoded as arbitrary squares.
//!
//! This isn't a true basis, since some products of squares vanish.
//! It is, however, a useful intermediary form for when Adem reduction
//! is too much of an overhead.

use std::ops::Mul;
use std::fmt::{Display, Formatter, Result as FResult};

use std::slice::{Iter as VIter};
use std::iter::Rev;

use linked_hash_set::{LinkedHashSet, Iter as LHSIter};

use super::{Cartan, Milnor};
use super::milnor::MilnorBasis;

/// A basis element of the Steenrod algebra, encoded as an arbitrary iterated
/// nontrivial squares `Sq^(...)`.
///
/// To compare these elements for equality inside the Steenrod algebra, first
/// convert them to Cartan or Milnor form.
#[derive(Clone, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SquareBasis(
    // Note: there are *no* invariants on this vector, other than
    // all elements being nonzero. elements are stored in the same
    // order as Cartan form
    Vec<usize>
);

impl SquareBasis {

    pub fn new(powers: &[usize]) -> SquareBasis {
        SquareBasis::from_vec(powers.into())
    }

    pub fn from_vec(mut powers: Vec<usize>) -> SquareBasis {
        powers.retain(|x| *x != 0);
        SquareBasis(powers)
    }

    /// An iterator over the squares in this basis element, in order
    /// of application, i.e., iterating on `Sq^(i1,...,ik)` will
    /// return `Sq^ik` first.
    pub fn iter(&self) -> Rev<VIter<usize>> {
        self.0.iter().rev()
    }

    /// Convert this basis element into a square sum.
    pub fn into_sum(self) -> Square {
        let mut result = Square::zero();
        result.0.insert(self);
        result
    }
}

impl<'a, 'b> Mul<&'b SquareBasis> for &'a SquareBasis {
    type Output = SquareBasis;

    fn mul(self, that: &'b SquareBasis) -> Self::Output {
        let mut res = self.clone();
        res.0.extend(that.iter().map(|x| *x));
        res
    }
}

extra_mul!(SquareBasis);

impl Display for SquareBasis {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        write!(f, "{}", self.0.iter().map(|x| format!("Sq^{}", x)).collect::<Vec<_>>().join(" "))
    }
}

/// An element of the Steenrod algebra, encoded as a sum of
/// arbitrary products of Steenrod squares.
///
/// To compare these elements for equality inside the Steenrod algebra, first
/// convert them to Cartan or Milnor form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Square(
    // each element corresponds to a product of
    // Steenrod squares, whose elements are the r in Sq^r
    // we store things in a hash set since it makes addition
    // easier and we're only working mod 2
    LinkedHashSet<SquareBasis>,
);


impl Square {

    /// Get the zero element in this basis.
    pub fn zero() -> Square {
        Square(LinkedHashSet::new())
    }

    /// Create a new element as a sum of Milnor basis elements.
    pub fn sum_of(vec: Vec<Vec<usize>>) -> Square {
        let mut res = Square::zero();
        for xs in vec {
            let op = SquareBasis::from_vec(xs);
            if !res.0.remove(&op) {
                res.0.insert(op);
            }
        }
        res
    }

    /// An iterator over the summands of this Steenrod element.
    pub fn iter(&self) -> LHSIter<SquareBasis> {
        self.0.iter()
    }

    pub fn to_cartan(&self) -> Cartan {
        Cartan::sum_of(self.iter().map(|sq| sq.0.iter().map(|x| *x).collect::<Vec<_>>()).collect::<Vec<_>>())
    }

    pub fn to_milnor(&self) -> Milnor {
        let mut milnor = Milnor::zero();
        for op in self.iter() {
            if op.0.is_empty() {
                continue
            }
            let mut prod = Milnor::zero();
            let mut iter = op.iter();
            prod += milnor!(*iter.next().unwrap());
            for r in iter {
                let mut next = Milnor::zero();
                for x in prod.iter() {
                    next += MilnorBasis::new(&[*r]) * x;
                }
                prod = next;
            }
            milnor += prod;
        }
        milnor
    }
}

vector_additon!(Square, Square, SquareBasis, SquareBasis::clone);

impl Display for Square {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        if self.0.is_empty() {
            write!(f, "0")
        } else {
            let mut copy = self.0.iter().map(SquareBasis::clone).collect::<Vec<_>>();
            copy.sort();
            write!(f, "{}", copy.iter()
                .map(|op| format!("{}", op))
                .collect::<Vec<_>>()
                .join(" + "))
        }
    }
}
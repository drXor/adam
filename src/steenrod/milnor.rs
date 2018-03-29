//! Steenrod operations, encoded in the Milnor basis.
//!
//! This basis is useful for efficient multiplication, without
//! resorting the the Adem relations.
//!
//! A theorem of Milnor tells us that `A*` is a polynomial algebra in
//! generators `\xi_k`, each in degree `2^k - 1`. The Milnor basis is
//! the dual of these generators. You can obtain what power `\xi_k` is
//! raised to with index notation: `a[k]`.

use std::ops::{Mul, Index};

use std::fmt::{Display, Formatter, Result as FResult};

use linked_hash_set::{LinkedHashSet, Iter as LHSIter};

use super::{Cartan, Square};

#[inline]
fn generator_degree(r: usize) -> usize {
    (2 << r) - 1
}

/// A basis element of the Steenrod algebra, encoded in the Milnor basis.
#[derive(Clone, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MilnorBasis(
    // important invariant: this vector should never have leading zeroes!
    Vec<usize>
);

impl MilnorBasis {

    /// Create a new operation from powers for an explicit Milnor basis.
    #[inline]
    pub fn new(powers: &[usize]) -> MilnorBasis {
        MilnorBasis::from_vec(powers.into())
    }

    /// Create a new operation from an existing allocation.
    pub fn from_vec(vec: Vec<usize>) -> MilnorBasis {
        let mut op = MilnorBasis(vec);
        op.trim();
        op
    }

    #[inline]
    fn trim(&mut self) {
        while let Some(&0) = self.0.last() {
            self.0.pop();
        }
    }

    /// The degree of this basis element in the Steenrod algebra.
    pub fn degree(&self) -> usize {
        let mut deg = 0;
        for (i, r) in self.0.iter().enumerate() {
            deg += r * generator_degree(i);
        }
        deg
    }

    /// Create a new iterator
    pub fn iter(&self) -> MilnorBasisIter {
        MilnorBasisIter { cur: self.clone() }
    }

    /// The length of this basis element, i.e. the largest `\xi_k`
    /// needed to represent it.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
        /*self.0.iter()
            .enumerate()
            .rev()
            .find(|&(_, r)| *r != 0)
            .map(|(i, _)| i + 1)
            .unwrap_or(0)*/
    }

    /// Convert this basis element into a Milnor sum.
    pub fn into_sum(self) -> Milnor {
        let mut result = Milnor::zero();
        result.0.insert(self);
        result
    }

    /// Sets the power of the generator dual `\xi_k`  to
    /// `power`. We implement this rather than `IndexMut` for
    /// technical reasons.
    pub fn set_power(&mut self, k: usize, power: usize) {
        if k < self.len() {
            self.0[k] = power;
            self.trim();
        } else if power > 0 {
            for _ in self.len() .. k {
                self.0.push(0)
            }
            self.0.push(power);
        }
    }
}

impl Index<usize> for MilnorBasis {
    type Output = usize;
    fn index(&self, index: usize) -> &Self::Output {
        if self.0.len() <= index {
            &0
        } else {
            &self.0[index]
        }
    }
}

impl<'a, 'b> Mul<&'b MilnorBasis> for &'a MilnorBasis {
    type Output = Milnor;

    fn mul(self, that: &'b MilnorBasis) -> Self::Output {

        // Multiplication is preformed by the following formula:
        // RS = sum_X b(X) T(X),
        // where X is a matrix whose rows sum to R and whose columns
        // sum to S, i.e.
        // R(X)[r] = sum_i 2^i X[r][i]
        // S(X)[r] = sum_i X[i][r]
        //
        // b(X) is the mod-2 product of the multinomial coefficients of
        // the perpendicular diagonals:
        // b(X) = prod_i (X[r-i][i]) mod 2
        // we can simplify this product to just checking that none of the
        // factors have a pairwise non-zero logical and; if they do, the
        // whole product vanishes.
        //
        // T(X) is a vector whose entries are the sums of each skew diagonal
        // of the matrix.
        //
        // This whole things comes out to being polynomial time, somehow.
        // Possibly memoize in the future?
        //
        // Reference: http://www.math.wayne.edu/~rrb/papers/adams.pdf, page 16

        use std::cmp::min;

        let max_rows = self.len();
        let max_cols = that.len();

        // allocate space for the matrix. we're going to get the most
        // we can out of this memory
        let mut matrix = vec![vec![0; max_cols + 1]; max_rows + 1];

        for i in 0..max_rows {
            matrix[i + 1][0] = self[i]
        }

        for i in 0..max_cols {
            matrix[0][i + 1] = that[i]
        }

        let mut result = Milnor::zero();

        // allocate some scratch space for assembling resulting squares
        let mut scratch = vec![0; max_rows + max_cols];

        #[inline]
        fn next_sq(max_rows: usize, max_cols: usize,
                   scratch: &mut Vec<usize>, matrix: &Vec<Vec<usize>>) -> bool {
            //println!("{:?}", matrix);
            for d in (1..scratch.len()+1).rev() {
                let mut row = min(max_rows, d);
                let mut col = d - row;
                scratch[d - 1] = matrix[row][col];
                let col_limit = min(max_cols, d);
                while col < col_limit {
                    col += 1;
                    row -= 1;
                    //println!("{:?}", (row, col));
                    //println!("{:?}", (col_limit));
                    if scratch[d - 1] & matrix[row][col] != 0 {
                        return false
                    } else {
                        scratch[d - 1] += matrix[row][col]
                    }
                }
            }
            true
        }

        #[inline]
        fn next_matrix(max_rows: usize, max_cols: usize, matrix: &mut Vec<Vec<usize>>) -> bool {
            for row in 1..max_rows + 1 {
                for col in 1..max_cols + 1 {
                    if matrix[0][col] != 0 && matrix[row][0] >> col != 0 {
                        matrix[row][col] += 1;
                        matrix[row][0] -= 1 << col;
                        matrix[0][col] -= 1;
                        return false
                    } else {
                        matrix[0][col] += matrix[row][col];
                        matrix[row][0] += matrix[row][col] << col;
                        matrix[row][col] = 0;
                    }
                }
            }
            true
        }

        loop {
            if next_sq(max_rows, max_cols, &mut scratch, &matrix) {
                // we don't need to validate mod 2 addition
                result.0.insert(MilnorBasis::from_vec(scratch.clone()));
            }

            if next_matrix(max_rows, max_cols, &mut matrix) {
                break;
            }
        }

        result
    }
}

extra_mul!(MilnorBasis);

impl Display for MilnorBasis {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        write!(f, "Sq({})", self.0.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().join(", "))
    }
}

/// An iterator on the Milnor basis. Iteration is performed in
/// lexicographic order of the generators.
pub struct MilnorBasisIter {
    cur: MilnorBasis,
}

impl Iterator for MilnorBasisIter {

    type Item = MilnorBasis;
    fn next(&mut self) -> Option<Self::Item> {
        {
            let next = &mut self.cur;
            for i in 0.. {
                if next.0.len() <= i {
                    next.0.push(0)
                }
                if next.0[0] >= generator_degree(i) {
                    next.0[0] -= generator_degree(i);
                    next.0[i] += 1;
                    break
                } else {
                    next.0[0] += next.0[i] * generator_degree(i);
                    next.0[i] = 0;
                }
            }
            while next.0.len() > 1 && *next.0.last().unwrap() == 0 {
                next.0.pop();
            }
        }
        self.cur.trim();
        Some(self.cur.clone())
    }
}

/// An element of the Steenrod algebra, encoded as a sum
/// of Milnor basis elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Milnor(
    // we can use a hashset, since this is a sum mod 2
    LinkedHashSet<MilnorBasis>,
);

impl Milnor {

    /// Get the zero element in this basis.
    pub fn zero() -> Milnor {
        Milnor(LinkedHashSet::new())
    }

    /// Create a new element as a sum of Milnor basis elements.
    pub fn sum_of(vec: Vec<MilnorBasis>) -> Milnor {
        let mut res = Milnor::zero();
        for x in vec {
            // we don't copy the vec, to ensure that we
            // correctly deal with repeats.
            res += x;
        }
        res
    }

    /// An iterator over the summands of this Steenrod element.
    pub fn iter(&self) -> LHSIter<MilnorBasis> {
        self.0.iter()
    }

    /// Convert this Steenrod element to the Cartan basis.
    pub fn to_cartan(&self) -> Cartan {
        self.to_square().to_cartan()
    }

    /// Convert this Steenrod element to a sum of squares.
    pub fn to_square(&self) -> Square {
        fn inner(mut orig: Milnor) -> Vec<Vec<usize>> {
            let mut total = Vec::new();
            while !orig.0.is_empty() {
                // pick a basis element from the sum
                // TODO: make this not clone()
                let op = orig.0.iter().next().unwrap().clone();
                let len = op.len();
                match len {
                    0 => {} // it's just a one
                    1 => {
                        total.push(vec![op[0]]);
                        orig += op;
                    }
                    _ => {
                        // op = Sq(r1,...,rk), then
                        // rr = Sq(r1,...,r(k-1) + rk)
                        // s  = Sq^(rk * 2^(k-1))
                        // y  = cartan(rr) * s

                        // add Sq(r) * rr to total and subtract it from orig
                        let mut last = op[len - 1];
                        let mut rr = op.clone();
                        rr.set_power(len - 1, 0);
                        let rr2 = rr[len - 2] + last;
                        rr.set_power(len - 2, rr2);
                        last <<= len - 1;

                        let s = MilnorBasis::new(&[last]);
                        orig += s * &rr;
                        let mut y = inner(rr.into_sum());

                        total.extend(y.iter().map(|op| {
                            let mut op = op.clone();
                            op.insert(0, last);
                            op
                        }));
                    }
                }
            }
            total
        }
        Square::sum_of(inner(self.clone()))
    }
}

vector_additon!(Milnor, Milnor, MilnorBasis, MilnorBasis::clone);

impl Display for Milnor {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        if self.0.is_empty() {
            write!(f, "0")
        } else {
            let mut copy = self.0.iter().map(MilnorBasis::clone).collect::<Vec<_>>();
            copy.sort();
            write!(f, "{}", copy.iter()
                .map(|op| format!("{}", op))
                .collect::<Vec<_>>()
                .join(" + "))
        }
    }
}
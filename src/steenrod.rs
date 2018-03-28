//! The Steenrod algebra, and related operations.
//!
//! The Steenrod alrebra consists of all cohomology operations
//! `H^*(X; F_2) -> H^*(X; F_2)` for some space `X`, though
//! its structure is independent of this space.

use std::ops::{Mul, Index, IndexMut};

#[inline]
fn generator_degree(r: usize) -> usize {
    (2 << r) - 1
}

/// A cohomology operation, i.e., a basis element of the Steenrod algebra.
///
/// A theorem of Milnor tells us that `A*` is a polynomial algebra in
/// generators `\xi_k`, each in degree `2^k - 1`. The Milnor basis is
/// the dual of these generators. You can obtain what power `\xi_k` is
/// raised to with index notation: `a[k]`.
#[derive(Clone, PartialEq, Hash, Debug)]
pub struct Sq(Vec<usize>);

impl Sq {

    /// Create a new operation from powers for an explicit Milnor basis.
    pub fn new(powers: &[usize]) -> Sq {
        Sq(powers.into())
    }

    pub fn from_vec(vec: Vec<usize>) -> Sq {
        Sq(vec)
    }

    /// The degree of this Sq in the Steenrod algebra.
    pub fn degree(&self) -> usize {
        let mut deg = 0;
        for (i, r) in self.0.iter().enumerate() {
            deg += r * generator_degree(i);
        }
        deg
    }

    /// Create a new iterator
    pub fn iter(&self) -> Iter {
        Iter { cur: self.clone() }
    }

    /// The length of this Sq, as a product of generators
    pub fn len(&self) -> usize {
        self.0.iter()
            .enumerate()
            .rev()
            .find(|&(_, r)| *r != 0)
            .map(|(i, _)| i + 1)
            .unwrap_or(0)
    }
}

impl Index<usize> for Sq {
    type Output = usize;
    fn index(&self, index: usize) -> &Self::Output {
        if self.0.len() <= index {
            &0
        } else {
            &self.0[index]
        }
    }
}

impl IndexMut<usize> for Sq {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        while self.0.len() <= index {
            self.0.push(0)
        }
        &mut self.0[index]
    }
}

// implement multiplication both for
// actual copies and references, for avoiding
// cloning as much as possible

impl<'a, 'b> Mul<&'b Sq> for &'a Sq {
    type Output = Vec<Sq>;

    fn mul(self, that: &'b Sq) -> Self::Output {

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
        // Reference: http://www.math.wayne.edu/~rrb/papers/adams.pdf, page 16

        use std::cmp::{max, min};

        // this is O(width^3)... we can probably make it faster, though
        #[inline]
        fn b(len: usize, matrix: &Vec<Vec<usize>>) -> bool {
            for r in 1..len+1 {
                for i in 0..matrix.len() {
                    // if we're out of bounds, don't index!
                    if r < i || r >= matrix.len() + i {
                        continue;
                    }
                    for j in 0..matrix.len() {
                        // if we're out of bounds, don't index!
                        if r < j || r >= matrix.len() + j {
                            continue;
                        }
                        if matrix[i][r-i] & matrix[i][r-i] != 0 {
                            return false;
                        }
                    }
                }
            }
            true
        }
        #[inline]
        fn T(len: usize, matrix: &Vec<Vec<usize>>) -> Sq {
            let mut vec = vec![0; len];
            for r in 1..len+1 {
                for i in 0..len {
                    // if we're out of bounds, don't index!
                    if i < 0 || i >= matrix.len() ||
                        r < i || r >= matrix.len() + i {
                        continue;
                    }
                    vec[r - 1] += matrix[i][r-i];
                }
            }
            Sq(vec)
        }

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

        let mut result = Vec::new();

        // allocate some scratch space for assembling resulting squares
        let mut scratch = vec![0; max_rows + max_cols];

        #[inline]
        fn next_sq(max_rows: usize, max_cols: usize,
                   scratch: &mut Vec<usize>, matrix: &Vec<Vec<usize>>) -> bool {
            println!("{:?}", matrix);
            for d in (1..scratch.len()+1).rev() {
                let mut row = min(max_rows, d);
                let mut col = d - row;
                scratch[d - 1] = matrix[row][col];
                let col_limit = min(max_cols, d);
                while col < col_limit {
                    col += 1;
                    row -= 1;
                    println!("{:?}", (row, col));
                    println!("{:?}", (col_limit));
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
                result.push(Sq(scratch.clone()))
            }

            if next_matrix(max_rows, max_cols, &mut matrix) {
                break;
            }
        }

        result
    }
}

impl Mul<Sq> for Sq {
    type Output = Vec<Sq>;
    fn mul(self, that: Sq) -> Self::Output {
        &self * &that
    }
}

impl<'a> Mul<&'a Sq> for Sq {
    type Output = Vec<Sq>;
    fn mul(self, that: &'a Sq) -> Self::Output {
        &self * that
    }
}

impl<'a> Mul<Sq> for &'a Sq {
    type Output = Vec<Sq>;
    fn mul(self, that: Sq) -> Self::Output {
        self * &that
    }
}

/// An iterator on the Milnor basis. Iteration is performed in
/// lexicographic order of the generators.
pub struct Iter {
    cur: Sq,
}

impl Iterator for Iter {

    type Item = Sq;
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
        Some(self.cur.clone())
    }
}
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

use bit_set::BitSet;

use super::{Cartan, Square};

#[inline]
fn generator_degree(r: usize) -> usize {
    (2 << r) - 1
}

fn d(k: usize, n: usize) -> usize {
    /*if k <= 2 {
        return 1 + n / 3
    } else {
        memo!(MEMO: (usize, usize), usize);
        memo_check!(MEMO, &(n, k));
        let mut sum = 0;
        loop {
            sum += d(k - 1, n);
            if n < generator_degree(k - 1) {
                break
            } else {
                n -= generator_degree(k - 1);
            }
        }
        memo_return!(MEMO, (n, k), sum);
    }*/
    powers_of_degree(n).iter()
        .filter(|xs| xs.len() <= k).count()
}

fn powers_of_degree(deg: usize) -> Vec<Vec<usize>> {

    use std::mem;

    memo!(MEMO: usize, Vec<Vec<usize>>);
    memo_check!(MEMO, &deg);

    let mut vec = Vec::new();
    let mut cur = vec![deg];
    vec.push(cur.clone());

    let max = mem::size_of::<usize>() * 8 - 1; // KLUDGE

    'a: loop {
        for i in 1..max {
            if cur[0] >= generator_degree(i) {
                cur[0] -= generator_degree(i);
                if i >= cur.len() {
                    cur.push(1);
                } else {
                    cur[i] += 1;
                }
                vec.push(cur.clone());
                continue 'a
            } else {
                if i < cur.len() {
                    cur[0] += cur[i] * generator_degree(i);
                    cur[i] = 0;
                }
            }
        }
        break
    }

    //println!("{}: {:?}", deg, vec);

    memo_return!(MEMO, deg, vec);
}

fn dim_of_degree(deg: usize) -> usize {

    use std::mem;

    memo!(MEMO: usize, usize);
    memo_check!(MEMO, &deg);

    memo_return!(MEMO, deg, powers_of_degree(deg).len());
}

const CHUNK_WIDTH: usize = 4;
const CHUNK_DATA_WIDTH: usize = 3;
const CHUNK_SIG_MASK: u32 = 0x8;
const CHUNK_DATA_MASK: u32 = 0x7;

fn compress_milnor(mut deg: u32, mut basis_num: u32) -> u64 {
    let mut res: u64 = 0;
    let mut shift = CHUNK_WIDTH;
    res |= CHUNK_SIG_MASK as u64;
    res |= (CHUNK_DATA_MASK & deg) as u64;
    deg >>= CHUNK_DATA_WIDTH;
    while deg != 0 {
        res <<= CHUNK_WIDTH;
        res |= (CHUNK_DATA_MASK & deg) as u64;
        deg >>= CHUNK_DATA_WIDTH;
        shift += CHUNK_WIDTH;
    }
    res |= (basis_num as u64) << shift;
    res
}

fn decompress_milnor(mut n: u64) -> (u32, u32) {
    let mut deg = 0;
    loop {
        deg |= (CHUNK_DATA_MASK & (n as u32));
        let done = (n as u32) & CHUNK_SIG_MASK != 0;
        n >>= CHUNK_WIDTH;
        if done {
            break
        } else {
            deg <<= CHUNK_DATA_WIDTH;
        }
    }
    (deg, n as u32)
}

/// A basis element of the Steenrod algebra, encoded in the Milnor basis.
// Implementation note: because each degree of A is finite, we can encode
// this as two ints: a degree, and which basis element of that slice of A
// it corresponds to.
#[derive(Clone, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MilnorBasis {
    // the degree of this basis element, given by
    // deg Sq^(r1,...,rk) = sum_i ri (2^i - 1)
    deg: usize,

    // the index of this element in the basis
    basis_number: usize,
}

impl MilnorBasis {

    /// Create a new operation from powers for an explicit Milnor basis.
    pub fn new(powers: &[usize]) -> MilnorBasis {

        let mut deg = 0;
        for (i, x) in powers.iter().enumerate() {
            deg += x * generator_degree(i);
        }

        let mut deg1 = deg;

        if powers.len() <= 1 {
            return MilnorBasis {
                deg,
                basis_number: 0,
            }
        }

        let powers = powers.into();

        memo!(MEMO: Vec<usize>, MilnorBasis);
        memo_check!(MEMO, &powers);

        let mut sum = 0;
        if powers.len() > 1 {
            for (i, x) in powers[2..].iter().rev().enumerate() {
                for _ in 0..*x {
                    sum += d(i, deg1);
                    deg1 -= generator_degree(i);
                }
            }
        }

        memo_return!(MEMO, powers, MilnorBasis {
            deg: deg,
            basis_number: sum + powers[1],
        });
    }

    /// Get the power representation `Sq^(r1,...,rk)` of this
    /// basis element.
    pub fn powers(&self) -> Vec<usize> {
        //println!("{:?}", self);
        powers_of_degree(self.deg).swap_remove(self.basis_number)

    }

    /// The degree of this basis element in the Steenrod algebra.
    #[inline]
    pub fn degree(&self) -> usize {
        self.deg
    }

    /// Convert this basis element into a Milnor sum.
    pub fn into_sum(self) -> Milnor {
        let mut res = Milnor::zero();
        res += self;
        res
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

        let self_powers = self.powers();
        let that_powers = that.powers();

        let max_rows = self_powers.len();
        let max_cols = that_powers.len();

        // allocate space for the matrix. we're going to get the most
        // we can out of this memory
        let mut matrix = vec![vec![0; max_cols + 1]; max_rows + 1];

        for i in 0..max_rows {
            matrix[i + 1][0] = self_powers[i]
        }

        for i in 0..max_cols {
            matrix[0][i + 1] = that_powers[i]
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
                result += MilnorBasis::new(&scratch[..]);
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
        write!(f, "Sq({})", self.powers().iter().map(|x| format!("{}", x)).collect::<Vec<_>>().join(", "))
    }
}

/// An element of the Steenrod algebra, encoded as a sum
/// of Milnor basis elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Milnor(
    // we can use a hashset, since this is a sum mod 2
    //LinkedHashSet<MilnorBasis>,
    BitSet
);

impl Milnor {

    /// Get the zero element in this basis.
    pub fn zero() -> Milnor {
        Milnor(BitSet::new())
    }

    pub fn dimension_of_degree(deg: usize) -> usize {
        dim_of_degree(deg)
    }

    pub fn basis_of_degree(deg: usize) -> Vec<MilnorBasis> {
        let mut vec = Vec::new();
        for i in 0..dim_of_degree(deg) {
            vec.push(MilnorBasis { deg, basis_number: i });
        }
        vec
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
    pub fn iter(&self) -> MilnorIter {
        MilnorIter { inner: self.0.iter() }
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
                let op = orig.iter().next().unwrap().powers();
                let len = op.len();
                match len {
                    0 => {} // it's just a one
                    1 => {
                        total.push(vec![op[0]]);
                        orig += MilnorBasis::new(&op[..]);
                    }
                    _ => {
                        // op = Sq(r1,...,rk), then
                        // rr = Sq(r1,...,r(k-1) + rk)
                        // s  = Sq^(rk * 2^(k-1))
                        // y  = cartan(rr) * s

                        // add Sq(r) * rr to total and subtract it from orig
                        let mut last = op[len - 1];
                        let mut rr = op.clone();
                        rr[len - 1] = 0;
                        let rr2 = rr[len - 2] + last;
                        rr[len - 2] = rr2;
                        last <<= len - 1;

                        let s = MilnorBasis::new(&[last]);
                        let rr_m = MilnorBasis::new(&rr);
                        orig += s * &rr_m;
                        let mut y = inner(rr_m.into_sum());

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

/// Iterator over a Milnor element.
pub struct MilnorIter<'a> {
    inner: ::bit_set::Iter<'a, u32>,
}

impl<'a> Iterator for MilnorIter<'a> {
    type Item = MilnorBasis;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|x| {
            let (n, k) = decompress_milnor(x as u64);
            MilnorBasis { deg: n as usize, basis_number: k as usize }
        })
    }
}

use std::ops::{ Add, AddAssign };

impl<'b> AddAssign<&'b Milnor> for Milnor {
    #[inline]
    fn add_assign(&mut self, that: &'b Milnor) {
        self.0.symmetric_difference_with(&that.0);
    }
}

impl<'b> AddAssign<MilnorBasis> for Milnor {
    #[inline]
    fn add_assign(&mut self, rhs: MilnorBasis) {
        let key = compress_milnor(rhs.deg as u32, rhs.basis_number as u32) as usize;
        if self.0.contains(key) {
            self.0.remove(key);
        } else {
            self.0.insert(key);
        }
    }
}

impl<'a, 'b> Add<&'b Milnor> for &'a Milnor {
    type Output = Milnor;
    #[inline]
    fn add(self, that: &'b Milnor) -> Milnor {
        let mut res = self.clone();
        res += that;
        res
    }
}

vector_add_extra!(Milnor);
vector_mul!(Milnor);

impl Display for Milnor {
    fn fmt(&self, f: &mut Formatter) -> FResult {
        if self.0.is_empty() {
            write!(f, "0")
        } else {
            let mut copy = self.iter().map(|x| x.clone()).collect::<Vec<_>>();
            copy.sort();
            write!(f, "{}", copy.iter()
                .map(|op| format!("{}", op))
                .collect::<Vec<_>>()
                .join(" + "))
        }
    }
}
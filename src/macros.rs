//! Macros

/// Assemble a Steenrod element in the Milnor basis, by specifying
/// a sum of zero or more Milnor basis elements:
///
/// ```
/// let op = milnor!([1, 2] + [3, 4]);
/// ```
///
#[macro_export]
macro_rules! milnor {
    () => { $crate::steenrod::Milnor::zero() };
    ([$($first:expr),* $(,)*] $(+ [$($rest:expr),* $(,)*])*) => {{
        $crate::steenrod::Milnor::sum_of(vec![
            $crate::steenrod::milnor::MilnorBasis::new(&[$($first),*]),
            $($crate::steenrod::milnor::MilnorBasis::new(&[$($rest),*])),*
        ])
    }};
    ($($first:expr),+ $(,)*) => { milnor!([$($first),+]) };
}

/// Assemble a Steenrod element in the Cartan basis, by specifying
/// a sum of zero or more Cartan basis elements:
///
/// ```
/// let op = cartan!([1, 2] + [3, 4]);
/// ```
///
#[macro_export]
macro_rules! cartan {
    () => { $crate::steenrod::Cartan::zero() };
    ([$($first:expr),* $(,)*] $(+ [$($rest:expr),* $(,)*])*) => {{
        $crate::steenrod::Cartan::sum_of(vec![
            vec![$($first),*],
            $(vec![$($rest),*]),*
        ])
    }};
    ($($first:expr),+ $(,)*) => { cartan!([$($first),+]) };
}

/// Assemble a Steenrod element as a sum of Steenrod squares.
///
/// ```
/// let op = square!([1, 2] + [3, 4]);
/// ```
///
#[macro_export]
macro_rules! square {
    () => { $crate::steenrod::Square::zero() };
    ([$($first:expr),* $(,)*] $(+ [$($rest:expr),* $(,)*])*) => {{
        $crate::steenrod::Square::sum_of(vec![
            vec![$($first),*],
            $(vec![$($rest),*]),*
        ])
    }};
    ($($first:expr),+ $(,)*) => { square!([$($first),+]) };
}

/// Assemble a module from generators and actions in one expression.
/// For example, the cohomology of RP4:
///
/// ```
/// let rp4 = module![
///     // four generators in degrees
///     // 1 through 4
///     1, 2, 3, 4;
///
///     // actions of the Steenrod squares on
///     // the ith generator
///     Sq(1) 0 => [1]
///     Sq(2) 1 => [3]
///     Sq(1) 2 => [3]
/// ];
/// ```
#[macro_export]
macro_rules! module {
    [
        $($generator:expr),* $(,)*;
        $(Sq($sq:expr) $input:expr => [$($output:expr),* $(,)*])*
    ] => {{
        let mut module = $crate::module::Module::new(vec![$($generator),+]);
        $(
            module.add_action($sq, $input, vec![$($output),*]);
        )*
        module
    }}
}
use rec::rec;

/// A valid rec expression shall be one of the following:
///     1) a character literal
///     2) a string literal
///     3) a path expression that resolves to a const [`&str`]
///     4) a grouped expression with an inner expression that is a valid rec expression
///     5) a bitwise NOT operator expression with a sub-expression that is a valid [`class
///        expression`]
///     6) a bitwise AND operator expression with sub-expressions that are all valid [`class
///        expression`]s
///     7) an addition or bitwise OR expression with sub-expressions that are all valid [`rec expression`]s
///     8) a range inclusive expression with bounds that are both character literals
///     9) a repeating array expression with a first sub-expression that is a valid [`rec expression`] and a second sub-expression that is a valid [`rep expression`]
#[test]
fn valid_rec() {
    #[rec]
    const CHAR: &str = 'a';

    #[rec]
    const STR: &str = "test";

    #[rec]
    const PATH: &str = CHAR;

    #[rec]
    const GROUP: &str = ('a');

    #[rec]
    const BITWISE_NOT: &str = !'a';

    #[rec]
    const ADDITION: &str = 'a' + 'b';

    #[rec]
    const BITWISE_OR: &str = 'a' | 'b';

    #[rec]
    const BITWISE_AND: &str = 'a' & 'b';

    #[rec]
    const RANGE: &str = 'a'..='b';

    #[rec]
    const REPEAT: &str = ['a'; ..];
}

/// A class expression shall be one of the following:
///     1) a character literal
///     2) a bitwise NOT expression with a sub-expression that is a [`class expression`]
///     3) a grouped expression with an inner expression that is one of the following:
///         1) a range inclusive expression with each bound being a character literal
///         2) a bitwise OR expression with each sub-expression being a [`class expression`]
///         3) a bitwise AND expression with each sub-expression being a [`class expression`]
#[test]
fn valid_class() {
    // The sub-expression of a bitwise NOT expression must be a class expression.
    #[rec]
    const NOT_CHAR: &str = !'a';

    #[rec]
    const NOT_RANGE: &str = !('a'..'c');

    #[rec]
    const NOT_OR: &str = !('a' | 'c');

    #[rec]
    const NOT_AND: &str = !('a' & 'c');

    #[rec]
    const NOT_NOT: &str = !!'a';
}

/// A valid rep expression shall be one of the following:
///     1) an integer literal
///     2) a range expression where each bound that is provided is an integer literal
///     3) a call expression where the function is "lazy" and the call params is a range expression as described by 2)
#[test]
fn valid_rep() {
    #[rec]
    const INTEGER: &str = ['a'; 1];

    #[rec]
    const RANGE: &str = ['a'; 1..3];

    #[rec]
    const RANGE_FROM: &str = ['a'; ..2];

    #[rec]
    const RANGE_TO: &str = ['a'; 1..];

    #[rec]
    const RANGE_FULL: &str = ['a'; ..];

    #[rec]
    const RANGE_INCLUSIVE: &str = ['a'; 1..=2];

    #[rec]
    const RANGE_TO_INCLUSIVE: &str = ['a'; ..=1];

    #[rec]
    const LAZY_RANGE: &str = ['a'; lazy(1..3)];

    #[rec]
    const LAZY_RANGE_FROM: &str = ['a'; lazy(..2)];

    #[rec]
    const LAZY_RANGE_TO: &str = ['a'; lazy(1..)];

    #[rec]
    const LAZY_RANGE_FULL: &str = ['a'; lazy(..)];

    #[rec]
    const LAZY_RANGE_INCLUSIVE: &str = ['a'; lazy(1..=2)];

    #[rec]
    const LAZY_RANGE_TO_INCLUSIVE: &str = ['a'; lazy(..=1)];
}

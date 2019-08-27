use rec::rec;

/// A range inclusive expression with bounds that are both character literals shall be converted to a character class that matches all characters between and including the bounds.
#[test]
fn range() {
    #[rec]
    const RANGE: &str = 'a'..='z';
    assert_eq!(RANGE, "[a-z]");
}

/// A bitwise OR expression with 2 [`class expression`]s shall be converted to a character class that matches all characters that either [`class expression`] matches.
#[test]
fn union() {
    #[rec]
    const UNITE_CHARS: &str = 'a' | 'c';
    assert_eq!(UNITE_CHARS, "[ac]");

    #[rec]
    const UNITE_RANGE_AND_CHAR: &str = ('0'..'9') | 'a';
    assert_eq!(UNITE_RANGE_AND_CHAR, "[0-9a]");

    #[rec]
    const UNITE_CHAR_AND_RANGE: &str = 'a' | ('0'..'9');
    assert_eq!(UNITE_CHAR_AND_RANGE, "[0-9a]");

    #[rec]
    const UNITE_UNION: &str = 'a' | 'x' | 'z';
    assert_eq!(UNITE_UNION, "[axz]");
}

/// A bitwise AND expression with 2 [`class expression`]s shall be converted to a character class that matches all characters that both [`class expression`]s match.
#[test]
fn intersection() {
    #[rec]
    const INTERSECT_CHAR_AND_CHAR: &str = 'a' & 'a';
    assert_eq!(INTERSECT_CHAR_AND_CHAR, "[a]");

    #[rec]
    const INTERSECT_CHAR_AND_UNION: &str = 'a' & ('a' | 'b');
    assert_eq!(INTERSECT_CHAR_AND_UNION, "[a]");

    #[rec]
    const INTERSECT_CHAR_AND_RANGE: &str = 'a' & ('a'..'e');
    assert_eq!(INTERSECT_CHAR_AND_RANGE, "[a]");

    #[rec]
    const INTERSECT_CHAR_AND_INTERSECTION: &str = 'a' & ('a' & 'a');
    assert_eq!(INTERSECT_CHAR_AND_INTERSECTION, "[a]");

    #[rec]
    const INTERSECT_CHAR_AND_NEGATION: &str = 'a' & !'b';
    assert_eq!(INTERSECT_CHAR_AND_NEGATION, "[a]");

    #[rec]
    const INTERSECT_TWO_RANGES: &str = ('a'..'e') & ('c'..'g');
    assert_eq!(INTERSECT_TWO_RANGES, "[c-e]");

    #[rec]
    const INTERSECT_RANGE_AND_UNION: &str = ('a'..'f') & ('a' | 'b');
    assert_eq!(INTERSECT_RANGE_AND_UNION, "[a-b]");

    #[rec]
    const INTERSECT_TWO_UNIONS: &str = ('a' | 'b') & ('a' | 'b' | 'c');
    assert_eq!(INTERSECT_TWO_UNIONS, "[a-b]");
}

/// A bitwise NOT expression with a [`class expression`] shall be converted to a character class that matches all characters except the characters that match the [`class expression`].
#[test]
fn negation() {
    #[rec]
    const NEGATE_CHAR: &str = !'b';
    assert_eq!(NEGATE_CHAR, "[\u{0}-ac-\u{10ffff}]");

    #[rec]
    const NEGATE_RANGE: &str = !('w'..'y');
    assert_eq!(NEGATE_RANGE, "[\u{0}-vz-\u{10ffff}]");

    #[rec]
    const NEGATE_UNION: &str = !('b' | 'y');
    assert_eq!(NEGATE_UNION, "[\u{0}-ac-xz-\u{10ffff}]");

    #[rec]
    const NEGATE_INTERSECTION: &str = !(('b'..'d') & ('a'..'g'));
    assert_eq!(NEGATE_INTERSECTION, "[\u{0}-ae-\u{10ffff}]");

    #[rec]
    const NEGATE_NEGATION: &str = !!'b';
    assert_eq!(NEGATE_NEGATION, "[b]");
}

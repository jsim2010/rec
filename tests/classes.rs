use rec::rec;

#[test]
fn range() {
    #[rec]
    const RANGE: Rec = 'a'..'z';
    assert_eq!(RANGE.to_string(), "[a-z]");
}

#[test]
fn unite_chars() {
    #[rec]
    const SINGLE_UNION: Rec = 'a' | 'c';
    assert_eq!(SINGLE_UNION, "[ac]");
}

#[test]
fn unite_range_and_char() {
    #[rec]
    const RANGE_OR_CHAR: Rec = ('0'..'9') | 'a';
    assert_eq!(RANGE_OR_CHAR, "[0-9a]");
}

#[test]
fn unite_char_and_range() {
    #[rec]
    const CHAR_OR_RANGE: Rec = 'a' | ('0'..'9');
    assert_eq!(CHAR_OR_RANGE, "[0-9a]");
}

#[test]
fn unite_multiple_chars() {
    #[rec]
    const MULTIPLE_UNION: Rec = 'a' | 'x' | 'z';
    assert_eq!(MULTIPLE_UNION, "[axz]");
}

#[test]
fn intersect_char_and_union() {
    #[rec]
    const INTERSECT_CHAR_AND_UNION: Rec = 'a' & ('a' | 'b');
    assert_eq!(INTERSECT_CHAR_AND_UNION, "[a]");
}

#[test]
fn intersect_char_and_range() {
    #[rec]
    const INTERSECT_CHAR_AND_RANGE: Rec = 'a' & ('a'..'e');
    assert_eq!(INTERSECT_CHAR_AND_RANGE, "[a]");
}

#[test]
fn intersect_two_ranges() {
    #[rec]
    const INTERSECT_TWO_RANGES: Rec = ('a'..'e') & ('c'..'g');
    assert_eq!(INTERSECT_TWO_RANGES, "[c-e]");
}

#[test]
fn intersect_range_and_union() {
    #[rec]
    const INTERSECT_RANGE_AND_UNION: Rec = ('a'..'f') & ('a' | 'b');
    assert_eq!(INTERSECT_RANGE_AND_UNION, "[a-b]");
}

#[test]
fn intersect_two_unions() {
    #[rec]
    const INTERSECT_TWO_UNIONS: Rec = ('a' | 'b') & ('a' | 'b' | 'c');
    assert_eq!(INTERSECT_TWO_UNIONS, "[a-b]");
}

#[test]
fn negate_char() {
    #[rec]
    const NEGATE_CHAR: Rec = !'b';
    assert_eq!(NEGATE_CHAR, "[\u{0}-ac-\u{10ffff}]");
}

#[test]
fn negate_range() {
    #[rec]
    const NEGATE_RANGE: Rec = !('w'..'y');
    assert_eq!(NEGATE_RANGE, "[\u{0}-vz-\u{10ffff}]");
}

#[test]
fn negate_union() {
    #[rec]
    const NEGATE_UNION: Rec = !('b' | 'y');
    assert_eq!(NEGATE_UNION, "[\u{0}-ac-xz-\u{10ffff}]");
}

#[test]
fn negate_intersection() {
    #[rec]
    const NEGATE_INTERSECTION: Rec = !(('b'..'d') & ('a'..'g'));
    assert_eq!(NEGATE_INTERSECTION, "[\u{0}-ae-\u{10ffff}]");
}

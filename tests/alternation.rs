use rec::rec;

#[test]
fn single_char_or() {
    #[rec]
    const SINGLE_CHAR_OR: Rec = 'a' | 'z';
    assert_eq!(SINGLE_CHAR_OR, "[az]");
}

#[test]
fn multiple_char_or() {
    #[rec]
    const MULTIPLE_CHAR_OR: Rec = 'a' | 'x' | 'z';
    assert_eq!(MULTIPLE_CHAR_OR, "[axz]");
}

#[test]
fn range_or_char() {
    #[rec]
    const RANGE_OR_CHAR: Rec = ('0'..'9') | 'a';
    assert_eq!(RANGE_OR_CHAR, "[0-9a]");
}

#[test]
fn char_or_range() {
    #[rec]
    const CHAR_OR_RANGE: Rec = 'a' | ('0'..'9');
    assert_eq!(CHAR_OR_RANGE, "[0-9a]");
}

#[test]
fn multiple_range_char() {
    #[rec]
    const MULTIPLE_RANGE_CHAR: Rec = 'a' | 'b' | 'c';
    assert_eq!(MULTIPLE_RANGE_CHAR, "[a-c]");
}

#[test]
fn char_or_str() {
    #[rec]
    const CHAR_OR_STR: Rec = 'a' | "xyz";
    assert_eq!(CHAR_OR_STR, r"a|xyz");
}

#[test]
fn str_or_range() {
    #[rec]
    const STR_OR_RANGE: Rec = "abc" | ('x'..'z');
    assert_eq!(STR_OR_RANGE, r"abc|[x-z]");
}

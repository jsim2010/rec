use rec::rec;

/// A character literal shall be converted to its literal value.
#[test]
fn char() {
    #[rec]
    const CHAR: &str = 'a';
    assert_eq!(CHAR, "a");

    #[rec]
    const PERIOD: &str = '.';
    // Must escape "." in regular expression, otherwise it will be interpreted as a
    // metacharacter.
    assert_eq!(PERIOD, r"\.");
}

/// A string literal shall be converted to the concatenation of the literal values of each of its
/// characters.
#[test]
fn str() {
    #[rec]
    const STR: &str = "test";
    assert_eq!(STR, "test");

    #[rec]
    const SENTENCE: &str = "This is a test.";
    assert_eq!(SENTENCE, r"This is a test\.");
}

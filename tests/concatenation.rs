use rec::rec;

/// An addition expression with sub-expressions that are both valid [`rec expression`]s shall be
/// converted to a concatentation.
#[test]
fn concatentation() {
    #[rec]
    const SINGLE_PLUS: &str = 'a' + 'b';
    assert_eq!(SINGLE_PLUS, "ab");

    #[rec]
    const MULTIPLE_PLUS: &str = 'a' + "test" + ('0'..'9') + 'z';
    assert_eq!(MULTIPLE_PLUS, "atest[0-9]z");

    #[rec]
    const CONCAT_ALTERNATION: &str = ("first" | "second") + "end";
    assert_eq!(CONCAT_ALTERNATION, "(?:first|second)end");

    #[rec]
    const CONCAT_TWO_ALTERNATIONS: &str = ("first" | "second") + ("third" | "fourth");
    assert_eq!(CONCAT_TWO_ALTERNATIONS, "(?:first|second)(?:third|fourth)");
}

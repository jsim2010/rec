use rec::rec;

#[test]
fn single_plus() {
    #[rec]
    const SINGLE_PLUS: Rec = 'a' + 'b';
    assert_eq!(SINGLE_PLUS, "ab");
}

#[test]
fn multiple_plus() {
    #[rec]
    const MULTIPLE_PLUS: Rec = 'a' + "test" + ('0'..'9') + 'z';
    assert_eq!(MULTIPLE_PLUS, "atest[0-9]z")
}

#[test]
fn concat_alternation() {
    #[rec]
    const CONCAT_ALTERNATION: Rec = ("first" | "second") + "end";
    assert_eq!(CONCAT_ALTERNATION, "(?:first|second)end");
}

#[test]
fn concat_two_alternations() {
    #[rec]
    const CONCAT_TWO_ALTERNATIONS: Rec = ("first" | "second") + ("third" | "fourth");
    assert_eq!(CONCAT_TWO_ALTERNATIONS, "(?:first|second)(?:third|fourth)");
}

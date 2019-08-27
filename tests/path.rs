use rec::rec;

#[rec]
const DIGIT: Rec = '0'..'9';

/// A path expression that resolves to a const [`&str`] shall be equal to the resolved value.
#[test]
fn single_path() {
    #[rec]
    const NEW_DIGIT: Rec = DIGIT;
    assert_eq!(NEW_DIGIT, "[0-9]");
}

#[test]
#[ignore] // Waiting for implementation of const variable concatentation.
fn repeat_path() {
    //#[rec]
    //const SOME_DIGITS: Rec = [DIGIT; 1..];
    //assert_eq!(SOME_DIGITS, "[0-9]+");
}

#[test]
#[ignore] // Waiting for implementation of const variable concatentation.
fn alternate_with_path() {
    //#[rec]
    //const A_OR_DIGIT: Rec = 'a' | DIGIT;
    //assert_eq!(A_OR_DIGIT, "a|[0-9]");
}

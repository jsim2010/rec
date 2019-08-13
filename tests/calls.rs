use rec::rec;

#[rec]
const DIGIT: Rec = '0'..'9';

#[test]
fn single_call() {
    #[rec]
    const NEW_DIGIT: Rec = DIGIT;
    assert_eq!(DIGIT, "[0-9]");
}

#[test]
#[ignore] // Waiting for implementation of const variable concatentation.
fn call_repeat() {
    //#[rec]
    //const SOME_DIGITS: Rec = [DIGIT; 1..];
    //assert_eq!(SOME_DIGITS, "[0-9]+");
}

#[test]
#[ignore] // Waiting for implementation of const variable concatentation.
fn alternate_with_call() {
    //#[rec]
    //const A_OR_DIGIT: Rec = 'a' | DIGIT;
    //assert_eq!(A_OR_DIGIT, "a|[0-9]");
}

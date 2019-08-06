use rec::rec;

rec! {single_plus_re = 'a' + 'b'}
rec! {multiple_plus_re = 'a' + "test" + ('0'..'9') + 'z'}

#[test]
fn single_plus() {
    assert_eq!(single_plus_re(), "ab");
}

#[test]
fn multiple_plus() {
    assert_eq!(multiple_plus_re(), "atest[0-9]z")
}

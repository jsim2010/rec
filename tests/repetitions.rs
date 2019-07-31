use rec::prelude::*;

#[test]
fn greedy_repeat_zero_or_more() {
    assert_eq!('x' * rpt(..), Rec::from("x*"));
}

#[test]
fn lazy_repeat_zero_or_more() {
    assert_eq!('x' / rpt(..), Rec::from("x*?"));
}

#[test]
fn greedy_repeat_one_or_more() {
    assert_eq!('x' * rpt(1..), Rec::from("x+"));
}

#[test]
fn lazy_repeat_one_or_more() {
    assert_eq!('x' / rpt(1..), Rec::from("x+?"));
}

#[test]
fn greedy_repeat_zero_or_one() {
    assert_eq!('x' * rpt(..=1), Rec::from("x?"));
}

#[test]
fn lazy_repeat_zero_or_one() {
    assert_eq!('x' / rpt(..=1), Rec::from("x??"));
}

#[test]
fn greedy_repeat_at_least_and_at_most() {
    assert_eq!('x' * rpt(3..=5), Rec::from("x{3,5}"));
}

#[test]
fn lazy_repeat_at_least_and_at_most() {
    assert_eq!('x' / rpt(3..=5), Rec::from("x{3,5}?"));
}

#[test]
fn greedy_repeat_at_least() {
    assert_eq!('x' * rpt(2..), Rec::from("x{2,}"));
}

#[test]
fn lazy_repeat_at_least() {
    assert_eq!('x' / rpt(2..), Rec::from("x{2,}?"));
}

#[test]
fn greedy_repeat_at_most() {
    assert_eq!('x' * rpt(..=4), Rec::from("x{0,4}"));
}

#[test]
fn lazy_repeat_at_most() {
    assert_eq!('x' / rpt(..=4), Rec::from("x{0,4}?"));
}

#[test]
fn repeat_exact() {
    assert_eq!('x' * rpt(3), Rec::from("x{3}"));
    assert_eq!('x' / rpt(3), Rec::from("x{3}"));
}

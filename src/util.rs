pub fn modulus(a: isize, b: isize) -> usize {
    assert!(b > 0);
    let t = a % b;
    if t >= 0 { t as usize } else { (t + b) as usize }
}
#[test]
fn modulus_test() {
    assert_eq!(modulus(-7, 5), 3);
    assert_eq!(modulus(-6, 5), 4);
    assert_eq!(modulus(-5, 5), 0);
    assert_eq!(modulus(-4, 5), 1);
    assert_eq!(modulus(-3, 5), 2);
    assert_eq!(modulus(-2, 5), 3);
    assert_eq!(modulus(-1, 5), 4);
    assert_eq!(modulus(0, 5), 0);
    assert_eq!(modulus(1, 5), 1);
    assert_eq!(modulus(2, 5), 2);
    assert_eq!(modulus(3, 5), 3);
    assert_eq!(modulus(4, 5), 4);
    assert_eq!(modulus(5, 5), 0);
    assert_eq!(modulus(6, 5), 1);
    assert_eq!(modulus(7, 5), 2);
}

pub fn count_equal<T>(arr_1: &[T], arr_2: &[T]) -> usize
where T: PartialOrd
{
    let mut pos = 0;
    let mut count = 0;

    for val in arr_1 {
        while pos < arr_2.len() && val > &arr_2[pos] { pos += 1; }
        if pos >= arr_2.len() { break; }
        if val == &arr_2[pos] { count += 1; }
    }

    count
}
#[test]
fn test_count_equal() {
    assert_eq!(count_equal(&[0;0], &[]), 0);
    assert_eq!(count_equal(&[1], &[]), 0);
    assert_eq!(count_equal(&[1, 2], &[]), 0);
    assert_eq!(count_equal(&[], &[2]), 0);
    assert_eq!(count_equal(&[], &[2, 3]), 0);

    assert_eq!(count_equal(&[1, 2, 3], &[4, 5, 6]), 0);
    assert_eq!(count_equal(&[1], &[4, 5, 6]), 0);
    assert_eq!(count_equal(&[1, 2, 3], &[4, 5, 6, 7, 8, 9]), 0);
    // symmetric
    assert_eq!(count_equal(&[4, 5, 6], &[1, 2, 3]), 0);
    assert_eq!(count_equal(&[4, 5, 6], &[1]), 0);
    assert_eq!(count_equal(&[4, 5, 6, 7, 8, 9], &[1, 2, 3]), 0);

    assert_eq!(count_equal(&[1, 2, 3], &[1, 5, 6]), 1);
    assert_eq!(count_equal(&[1, 2, 3], &[1, 5, 6]), 1);
    // symmetric
    assert_eq!(count_equal(&[1, 5, 6], &[1, 2, 3]), 1);
    assert_eq!(count_equal(&[1, 5, 6], &[1, 2, 3]), 1);

    assert_eq!(count_equal(&[1, 2, 3], &[1, 3, 5, 6]), 2);
    assert_eq!(count_equal(&[1, 2, 3], &[-5, -2, 1, 3, 5, 6]), 2);
    assert_eq!(count_equal(&[1, 2, 3], &[-5, -2, 0, 1, 3, 5, 6]), 2);
    // symmetric
    assert_eq!(count_equal(&[1, 3, 5, 6], &[1, 2, 3]), 2);
    assert_eq!(count_equal(&[-5, -2, 1, 3, 5, 6], &[1, 2, 3]), 2);
    assert_eq!(count_equal(&[-5, -2, 0, 1, 3, 5, 6], &[1, 2, 3]), 2);

    assert_eq!(count_equal(&[6, 16, 22, 23], &[6, 16, 22, 23]), 4);
    assert_eq!(count_equal(&[6, 16, 22, 23, 77], &[6, 16, 22, 23, 77]), 5);
    assert_eq!(count_equal(&[6, 16, 22, 23, 77, 102], &[6, 16, 22, 23, 77, 102]), 6);

    assert_eq!(count_equal(&[6, 16, 22, 23], &[6, 16, 17, 18, 19, 22, 23]), 4);
    assert_eq!(count_equal(&[6, 16, 22, 23, 77], &[6, 16, 22, 23, 24, 77]), 5);
    assert_eq!(count_equal(&[6, 16, 22, 23, 77, 102], &[6, 7, 16, 22, 23, 70, 71, 72, 77, 100, 102]), 6);
    // symmetric
    assert_eq!(count_equal(&[6, 16, 17, 18, 19, 22, 23], &[6, 16, 22, 23]), 4);
    assert_eq!(count_equal(&[6, 16, 22, 23, 24, 77], &[6, 16, 22, 23, 77]), 5);
    assert_eq!(count_equal(&[6, 7, 16, 22, 23, 70, 71, 72, 77, 100, 102], &[6, 16, 22, 23, 77, 102]), 6);

    assert_eq!(count_equal(&[10, 100, 1000], &[1, 2, 3]), 0);
    assert_eq!(count_equal(&[10, 100, 1000], &[15, 18, 90, 98, 99]), 0);
    assert_eq!(count_equal(&[10, 100, 1000], &[101, 104, 204, 598, 999]), 0);
    assert_eq!(count_equal(&[10, 100, 1000], &[100, 101, 104, 204, 598, 999]), 1);
    assert_eq!(count_equal(&[10, 100, 1000], &[101, 104, 204, 598, 999, 1000]), 1);
    assert_eq!(count_equal(&[10, 100, 1000], &[100, 101, 104, 204, 598, 999, 1000]), 2);
    assert_eq!(count_equal(&[10, 100, 1000], &[1002, 1044, 1843, 2948, 1934]), 0);
    assert_eq!(count_equal(&[10, 100, 1000], &[1000, 1002, 1044, 1843, 2948, 1934]), 1);
    assert_eq!(count_equal(&[10, 100, 1000], &[999, 1000, 1002, 1044, 1843, 2948, 1934]), 1);
    // symmetric
    assert_eq!(count_equal(&[1, 2, 3], &[10, 100, 1000]), 0);
    assert_eq!(count_equal(&[15, 18, 90, 98, 99], &[10, 100, 1000]), 0);
    assert_eq!(count_equal(&[101, 104, 204, 598, 999], &[10, 100, 1000]), 0);
    assert_eq!(count_equal(&[100, 101, 104, 204, 598, 999], &[10, 100, 1000]), 1);
    assert_eq!(count_equal(&[101, 104, 204, 598, 999, 1000], &[10, 100, 1000]), 1);
    assert_eq!(count_equal(&[100, 101, 104, 204, 598, 999, 1000], &[10, 100, 1000]), 2);
    assert_eq!(count_equal(&[1002, 1044, 1843, 2948, 1934], &[10, 100, 1000]), 0);
    assert_eq!(count_equal(&[1000, 1002, 1044, 1843, 2948, 1934], &[10, 100, 1000]), 1);
    assert_eq!(count_equal(&[999, 1000, 1002, 1044, 1843, 2948, 1934], &[10, 100, 1000]), 1);
}

// source: https://doc.rust-lang.org/std/ops/trait.Div.html
pub fn gcd(mut x: usize, mut y: usize) -> usize {
    while y != 0 {
        let t = y;
        y = x % y;
        x = t;
    }
    x
}
#[test]
fn test_gcd() {
    assert_eq!(gcd(1, 2), 1);
    assert_eq!(gcd(2, 3), 1);
    assert_eq!(gcd(3, 6), 3);
    assert_eq!(gcd(8, 24), 8);
    assert_eq!(gcd(11, 3), 1);
}

// Vec::is_sorted is nightly-only, so use this workaround
#[cfg(test)]
pub fn is_sorted<T: PartialOrd>(arr: &[T]) -> bool {
    for w in arr.windows(2) {
        if w[0] > w[1] {
            return false;
        }
    }
    true
}
#[test]
fn test_is_sorted() {
    assert!(is_sorted(&[1, 2, 3]));
    assert!(is_sorted(&[1, 3, 4]));
    assert!(!is_sorted(&[1, 4, 3]));
    assert!(!is_sorted(&[6, 3, 4]));
}
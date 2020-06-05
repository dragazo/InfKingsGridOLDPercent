use std::collections::BTreeSet;

use crate::util;

pub trait Set<T>: Default {
    fn clear(&mut self);
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn can_add(&self, code: &Vec<T>) -> bool;
    fn add(&mut self, code: Vec<T>) -> bool;
}

#[derive(Default)]
pub struct OLD<T>
where T: Ord + Default
{
    codes: BTreeSet<Vec<T>>,
}
impl<T> Set<T> for OLD<T>
where T: Ord + Default
{
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn is_empty(&self) -> bool {
        self.codes.is_empty()
    }
    fn len(&self) -> usize {
        self.codes.len()
    }
    fn can_add(&self, code: &Vec<T>) -> bool {
        !code.is_empty() && !self.codes.contains(code)
    }
    fn add(&mut self, code: Vec<T>) -> bool {
        if self.can_add(&code) {
            self.codes.insert(code);
            true
        }
        else { false }
    }
}

#[derive(Default)]
pub struct DET<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set<T> for DET<T>
where T: Ord + Default
{
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn is_empty(&self) -> bool {
        self.codes.is_empty()
    }
    fn len(&self) -> usize {
        self.codes.len()
    }
    fn can_add(&self, code: &Vec<T>) -> bool {
        if code.len() < 2 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, code);
            if equal + 2 > other.len() && equal + 2 > code.len() {
                return false;
            }
        }
        true
    }
    fn add(&mut self, code: Vec<T>) -> bool {
        if self.can_add(&code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

#[derive(Default)]
pub struct RED<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set<T> for RED<T>
where T: Ord + Default
{
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn is_empty(&self) -> bool {
        self.codes.is_empty()
    }
    fn len(&self) -> usize {
        self.codes.len()
    }
    fn can_add(&self, code: &Vec<T>) -> bool {
        if code.len() < 2 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, code);
            if other.len() + code.len() - 2 * equal < 2 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, code: Vec<T>) -> bool {
        if self.can_add(&code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

#[derive(Default)]
pub struct ERR<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set<T> for ERR<T>
where T: Ord + Default
{
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn is_empty(&self) -> bool {
        self.codes.is_empty()
    }
    fn len(&self) -> usize {
        self.codes.len()
    }
    fn can_add(&self, code: &Vec<T>) -> bool {
        if code.len() < 3 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, code);
            if other.len() + code.len() - 2 * equal < 3 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, code: Vec<T>) -> bool {
        if self.can_add(&code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

#[test]
fn test_det_set() {
    let mut s: DET<(isize, isize)> = Default::default();
    
    assert!(s.is_empty());
    assert!(!s.add(vec![]));
    assert!(s.is_empty());
    assert!(!s.add(vec![(0, 1)]));
    assert!(s.is_empty());
    
    assert!(s.add(vec![(0, 1), (0, 2)]));
    assert_eq!(s.len(), 1);
    assert!(!s.add(vec![(0, 1), (0, 2)]));
    assert_eq!(s.len(), 1);

    assert!(!s.add(vec![(0, 2), (0, 3)]));
    assert_eq!(s.len(), 1);

    assert!(s.add(vec![(0, 3), (0, 4)]));
    assert_eq!(s.len(), 2);

    assert!(!s.add(vec![(0, 2), (0, 5)]));
    assert_eq!(s.len(), 2);
    assert!(!s.add(vec![(0, 2), (0, 4)]));
    assert_eq!(s.len(), 2);

    assert!(!s.add(vec![(0, 3), (0, 4)]));
    assert_eq!(s.len(), 2);
    assert!(!s.add(vec![(0, 3), (0, 4), (0, 5)]));
    assert_eq!(s.len(), 2);
    assert!(s.add(vec![(0, 3), (0, 4), (0, 5), (0, 6)]));
    assert_eq!(s.len(), 3);

    assert!(s.add(vec![(0, 6), (1, 2)]));
    assert_eq!(s.len(), 4);
    assert!(s.add(vec![(0, 4), (1, 5), (1, 6)]));
    assert_eq!(s.len(), 5);
}
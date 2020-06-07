use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::util;

pub trait Set<T>: Default + Clone + Debug + PartialEq {
    const MIN_DOM: usize;

    fn clear(&mut self);
    fn can_add(&self, is_detector: bool, code: &Vec<T>) -> bool;
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool;
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct DOM<T>(std::marker::PhantomData<T>);
impl<T> Set<T> for DOM<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 1;

    fn clear(&mut self) {}
    fn can_add(&self, _is_detector: bool, code: &Vec<T>) -> bool {
        !code.is_empty()
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        self.can_add(is_detector, &code)
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct EDOM<T>(std::marker::PhantomData<T>);
impl<T> Set<T> for EDOM<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 1;

    fn clear(&mut self) {}
    fn can_add(&self, _is_detector: bool, code: &Vec<T>) -> bool {
        code.len() == 1
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        self.can_add(is_detector, &code)
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct LD<T>
where T: Ord
{
    codes: BTreeSet<Vec<T>>,
}
impl<T> Set<T> for LD<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 1;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, is_detector: bool, code: &Vec<T>) -> bool {
        is_detector || (!code.is_empty() && !self.codes.contains(code))
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        if self.can_add(is_detector, &code) {
            if !is_detector {
                self.codes.insert(code);
            }
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct OLD<T>
where T: Ord
{
    codes: BTreeSet<Vec<T>>,
}
impl<T> Set<T> for OLD<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 1;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, _is_detector: bool, code: &Vec<T>) -> bool {
        !code.is_empty() && !self.codes.contains(code)
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        if self.can_add(is_detector, &code) {
            self.codes.insert(code);
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct RED<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set<T> for RED<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 2;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, _is_detector: bool, code: &Vec<T>) -> bool {
        if code.len() < 2 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, code);
            if other.len() + code.len() - 2 * equal < 2 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        if self.can_add(is_detector, &code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct DET<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set<T> for DET<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 2;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, _is_detector: bool, code: &Vec<T>) -> bool {
        if code.len() < 2 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, code);
            if equal + 2 > other.len() && equal + 2 > code.len() {
                return false;
            }
        }
        true
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        if self.can_add(is_detector, &code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct ERR<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set<T> for ERR<T>
where T: Ord + Default + Clone + Debug
{
    const MIN_DOM: usize = 3;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, _is_detector: bool, code: &Vec<T>) -> bool {
        if code.len() < 3 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, code);
            if other.len() + code.len() - 2 * equal < 3 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, is_detector: bool, code: Vec<T>) -> bool {
        if self.can_add(is_detector, &code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

#[test]
fn test_det_set() {
    let mut s: DET<(isize, isize)> = Default::default();
    
    assert!(s.codes.is_empty());
    assert!(!s.add(false, vec![]));
    assert!(s.codes.is_empty());
    assert!(!s.add(false, vec![(0, 1)]));
    assert!(s.codes.is_empty());
    
    assert!(s.add(false, vec![(0, 1), (0, 2)]));
    assert_eq!(s.codes.len(), 1);
    assert!(!s.add(false, vec![(0, 1), (0, 2)]));
    assert_eq!(s.codes.len(), 1);

    assert!(!s.add(false, vec![(0, 2), (0, 3)]));
    assert_eq!(s.codes.len(), 1);

    assert!(s.add(false, vec![(0, 3), (0, 4)]));
    assert_eq!(s.codes.len(), 2);

    assert!(!s.add(false, vec![(0, 2), (0, 5)]));
    assert_eq!(s.codes.len(), 2);
    assert!(!s.add(false, vec![(0, 2), (0, 4)]));
    assert_eq!(s.codes.len(), 2);

    assert!(!s.add(false, vec![(0, 3), (0, 4)]));
    assert_eq!(s.codes.len(), 2);
    assert!(!s.add(false, vec![(0, 3), (0, 4), (0, 5)]));
    assert_eq!(s.codes.len(), 2);
    assert!(s.add(false, vec![(0, 3), (0, 4), (0, 5), (0, 6)]));
    assert_eq!(s.codes.len(), 3);

    assert!(s.add(false, vec![(0, 6), (1, 2)]));
    assert_eq!(s.codes.len(), 4);
    assert!(s.add(false, vec![(0, 4), (1, 5), (1, 6)]));
    assert_eq!(s.codes.len(), 5);
}
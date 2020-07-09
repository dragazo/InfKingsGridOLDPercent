use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::util;

pub trait LOC: Clone + Debug + PartialEq {
    type Item;

    fn dom(&self) -> usize;
    fn new(code: Vec<Self::Item>, is_detector: bool) -> Self;
}
pub trait Set: Default + Clone + Debug + PartialEq {
    type Item;
    type LocatingCode: LOC<Item = Self::Item>;

    fn clear(&mut self);
    fn can_add(&self, loc: &Self::LocatingCode) -> bool;
    fn add(&mut self, loc: Self::LocatingCode) -> bool;
}

#[derive(Clone, Debug, PartialEq)]
pub struct RegularLOC<T>
where T: Clone + Debug + PartialEq
{
    code: Vec<T>,
}
impl<T> LOC for RegularLOC<T>
where T: Clone + Debug + PartialEq
{
    type Item = T;

    fn dom(&self) -> usize {
        self.code.len()
    }
    fn new(code: Vec<T>, _: bool) -> Self {
        Self { code }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct LDLOC<T>
where T: Clone + Debug + PartialEq
{
    code: Vec<T>,
    is_detector: bool
}
impl<T> LOC for LDLOC<T>
where T: Clone + Debug + PartialEq
{
    type Item = T;

    fn dom(&self) -> usize {
        if self.is_detector {
            self.code.len() + 1
        }
        else {
            self.code.len()
        }
    }
    fn new(code: Vec<T>, is_detector: bool) -> Self {
        Self { code, is_detector }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct DOM<T>(std::marker::PhantomData<T>);
impl<T> Set for DOM<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = RegularLOC<T>;

    fn clear(&mut self) {}
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        !loc.code.is_empty()
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        self.can_add(&loc)
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct EDOM<T>(std::marker::PhantomData<T>);
impl<T> Set for EDOM<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = RegularLOC<T>;

    fn clear(&mut self) {}
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        loc.code.len() == 1
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        self.can_add(&loc)
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct LD<T>
where T: Ord
{
    codes: BTreeSet<Vec<T>>,
}
impl<T> Set for LD<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = LDLOC<T>;
    
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        loc.is_detector || (!loc.code.is_empty() && !self.codes.contains(&loc.code))
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        if self.can_add(&loc) {
            if !loc.is_detector {
                self.codes.insert(loc.code);
            }
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct DETLD<T>
where T: Ord
{
    detector_codes: BTreeSet<Vec<T>>,
    non_detector_codes: BTreeSet<Vec<T>>,
}
impl<T> Set for DETLD<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = LDLOC<T>;

    fn clear(&mut self) {
        self.non_detector_codes.clear();
        self.detector_codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.is_detector {
            // detectors must be at least 1-open-dominated
            if loc.code.len() < 1 {
                return false;
            }
            // must be 1-open-distinguished from other detectors
            if self.detector_codes.contains(&loc.code) {
                return false;
            }
            // must be asymmetrically sharp distinguished from non-detectors
            for other in self.non_detector_codes.iter() {
                let eq = util::count_equal(&loc.code, other);
                if other.len() - eq < 2 && loc.code.len() - eq < 1 {
                    return false;
                }
            }
        }
        else {
            // non-detectors must be at least 2-open-dominated
            if loc.code.len() < 2 {
                return false;
            }
            // must be asymmetrically sharp distinguished from detectors
            for other in self.detector_codes.iter() {
                let eq = util::count_equal(&loc.code, other);
                if loc.code.len() - eq < 2 && other.len() - eq < 1 {
                    return false;
                }
            }
            // must be 2-sharp distinguished from other non-detectors
            for other in self.non_detector_codes.iter() {
                if util::max_diff(&loc.code, other) < 2 {
                    return false;
                }
            }
        }
        true
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        if self.can_add(&loc) {
            // if it's valid add it in the right place (very important, otherwise constraints are broken)
            if loc.is_detector {
                self.detector_codes.insert(loc.code);
            }
            else {
                self.non_detector_codes.insert(loc.code);
            }
            true
        }
        else {
            false
        }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct OLD<T>
where T: Ord
{
    codes: BTreeSet<Vec<T>>,
}
impl<T> Set for OLD<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = RegularLOC<T>;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        !loc.code.is_empty() && !self.codes.contains(&loc.code)
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        if self.can_add(&loc) {
            self.codes.insert(loc.code);
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct RED<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set for RED<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = RegularLOC<T>;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.code.len() < 2 { return false; }
        for other in &self.codes {
            if util::symmetric_diff(other, &loc.code) < 2 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        if self.can_add(&loc) {
            self.codes.push(loc.code);
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct DET<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set for DET<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = RegularLOC<T>;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.code.len() < 2 { return false; }
        for other in &self.codes {
            if util::max_diff(other, &loc.code) < 2 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        if self.can_add(&loc) {
            self.codes.push(loc.code);
            true
        }
        else { false }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct ERR<T> {
    codes: Vec<Vec<T>>,
}
impl<T> Set for ERR<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = RegularLOC<T>;

    fn clear(&mut self) {
        self.codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.code.len() < 3 { return false; }
        for other in &self.codes {
            let equal = util::count_equal(other, &loc.code);
            if other.len() + loc.code.len() - 2 * equal < 3 {
                return false;
            }
        }
        true
    }
    fn add(&mut self, loc: Self::LocatingCode) -> bool {
        if self.can_add(&loc) {
            self.codes.push(loc.code);
            true
        }
        else { false }
    }
}

#[test]
fn test_det_set() {
    type C = <DET<(isize, isize)> as Set>::LocatingCode;
    let mut s: DET<(isize, isize)> = Default::default();
    
    assert!(s.codes.is_empty());
    assert!(!s.add(C::new(vec![], false)));
    assert!(s.codes.is_empty());
    assert!(!s.add(C::new(vec![(0, 1)], false)));
    assert!(s.codes.is_empty());
    
    assert!(s.add(C::new(vec![(0, 1), (0, 2)], false)));
    assert_eq!(s.codes.len(), 1);
    assert!(!s.add(C::new(vec![(0, 1), (0, 2)], false)));
    assert_eq!(s.codes.len(), 1);

    assert!(!s.add(C::new(vec![(0, 2), (0, 3)], false)));
    assert_eq!(s.codes.len(), 1);

    assert!(s.add(C::new(vec![(0, 3), (0, 4)], false)));
    assert_eq!(s.codes.len(), 2);

    assert!(!s.add(C::new(vec![(0, 2), (0, 5)], false)));
    assert_eq!(s.codes.len(), 2);
    assert!(!s.add(C::new(vec![(0, 2), (0, 4)], false)));
    assert_eq!(s.codes.len(), 2);

    assert!(!s.add(C::new(vec![(0, 3), (0, 4)], false)));
    assert_eq!(s.codes.len(), 2);
    assert!(!s.add(C::new(vec![(0, 3), (0, 4), (0, 5)], false)));
    assert_eq!(s.codes.len(), 2);
    assert!(s.add(C::new(vec![(0, 3), (0, 4), (0, 5), (0, 6)], false)));
    assert_eq!(s.codes.len(), 3);

    assert!(s.add(C::new(vec![(0, 6), (1, 2)], false)));
    assert_eq!(s.codes.len(), 4);
    assert!(s.add(C::new(vec![(0, 4), (1, 5), (1, 6)], false)));
    assert_eq!(s.codes.len(), 5);
}

#[test]
fn test_detld_set() {
    type S = DETLD<i32>;
    type C = <S as Set>::LocatingCode;

    let mut s = S::default();
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(vec![], true)));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);
    
    assert!(!s.add(C::new(vec![], false)));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(vec![1], false)));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(vec![1], true)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(vec![1], true)));
    assert!(!s.add(C::new(vec![1], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(vec![2, 3], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(vec![2, 3], true)));
    assert!(!s.add(C::new(vec![2, 3], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(vec![2, 4], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(vec![2, 4, 5], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(!s.add(C::new(vec![1, 6], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(vec![1, 6, 7], false)));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(vec![10, 11], true)));
    assert_eq!(s.detector_codes.len(), 2);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(!s.add(C::new(vec![3], true)));
    assert_eq!(s.detector_codes.len(), 2);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(vec![20], true)));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 3);
}

#[test]
fn ld_loc_test() {
    type C = LDLOC<i32>;

    assert_eq!(C::new(vec![1, 2, 3], false).dom(), 3);
    assert_eq!(C::new(vec![1, 2, 3], true).dom(), 4);

    assert_eq!(C::new(vec![1, 2, 3, -1, -2], false).dom(), 5);
    assert_eq!(C::new(vec![1, 2, 3, -1, -2], true).dom(), 6);
}

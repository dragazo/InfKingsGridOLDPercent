use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::util;

pub trait LOC: Clone + Debug + PartialEq {
    type Item;

    fn dom(&self) -> usize;
    fn new(pos: Self::Item, is_detector: bool, code: Vec<Self::Item>) -> Self;
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
    fn new(_: T, _: bool, code: Vec<T>) -> Self {
        Self { code }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct LDLOC<T>
where T: Clone + Debug + PartialEq
{
    code: Vec<T>,
    is_detector: bool,
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
    fn new(_: T, is_detector: bool, code: Vec<T>) -> Self {
        Self { code, is_detector }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct REDLDLOC<T>
where T: Clone + Debug + PartialEq
{
    code: Vec<T>,
    is_detector: bool,
    pos: T,
}
impl<T> LOC for REDLDLOC<T>
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
    fn new(pos: T, is_detector: bool, code: Vec<T>) -> Self {
        Self { pos, code, is_detector }
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
pub struct REDLD<T>
where T: Ord
{
    detector_codes: Vec<(T, Vec<T>)>,
    non_detector_codes: Vec<Vec<T>>,
}
impl<T> Set for REDLD<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = REDLDLOC<T>;

    fn clear(&mut self) {
        self.non_detector_codes.clear();
        self.detector_codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.is_detector {
            // detectors must be at least 1-open-dominated
            if loc.code.is_empty() {
                return false;
            }
            // any pair of detectors and non-detectors must be 1-open-distinguished by something other than the detector
            for other in self.non_detector_codes.iter() {
                let mut diff = util::symmetric_diff(&loc.code, other);
                if other.contains(&loc.pos) {
                    diff -= 1;
                }
                if diff < 1 {
                    return false;
                }
            }
        }
        else {
            // non-detectors must be at least 2-open-dominated
            if loc.code.len() < 2 {
                return false;
            }
            // any pair of detectors and non-detectors must be 1-open-distinguished by something other than the detector
            for other in self.detector_codes.iter() {
                let mut diff = util::symmetric_diff(&loc.code, &other.1);
                if loc.code.contains(&other.0) {
                    diff -= 1;
                }
                if diff < 1 {
                    return false;
                }
            }
            // non-detectors must be 2-open-distinguished
            for other in self.non_detector_codes.iter() {
                if util::symmetric_diff(&loc.code, other) < 2 {
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
                self.detector_codes.push((loc.pos, loc.code));
            }
            else {
                self.non_detector_codes.push(loc.code);
            }
            true
        }
        else {
            false
        }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct DETLD<T>
where T: Ord
{
    detector_codes: BTreeSet<Vec<T>>,
    non_detector_codes: Vec<Vec<T>>,
}
impl<T> Set for DETLD<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = LDLOC<T>;

    fn clear(&mut self) {
        self.detector_codes.clear();
        self.non_detector_codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.is_detector {
            // detectors must be at least 1-open-dominated
            if loc.code.is_empty() {
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
                self.non_detector_codes.push(loc.code);
            }
            true
        }
        else {
            false
        }
    }
}

#[derive(Default, Clone, Debug, PartialEq)]
pub struct ERRLD<T>
where T: Ord
{
    detector_codes: Vec<(T, Vec<T>)>,
    non_detector_codes: Vec<Vec<T>>,
}
impl<T> Set for ERRLD<T>
where T: Ord + Default + Clone + Debug
{
    type Item = T;
    type LocatingCode = REDLDLOC<T>;

    fn clear(&mut self) {
        self.non_detector_codes.clear();
        self.detector_codes.clear();
    }
    fn can_add(&self, loc: &Self::LocatingCode) -> bool {
        if loc.is_detector {
            // detectors must be at least 2-open-dominated
            if loc.code.len() < 2 {
                return false;
            }
            // detectors must be 1-open-distinguished by something other than each other
            for other in self.detector_codes.iter() {
                let mut diff = util::symmetric_diff(&loc.code, &other.1);
                if loc.code.contains(&other.0) {
                    diff -= 1;
                }
                if other.1.contains(&loc.pos) {
                    diff -= 1;
                }
                if diff < 1 {
                    return false;
                }
            }
            // detector/non-detectors must be 2-open-distinguished by something other than each other
            for other in self.non_detector_codes.iter() {
                let mut diff = util::symmetric_diff(&loc.code, other);
                if other.contains(&loc.pos) {
                    diff -= 1;
                }
                if diff < 2 {
                    return false;
                }
            }
        }
        else {
            // non-detectors must be at least 3-open-dominated
            if loc.code.len() < 3 {
                return false;
            }
            // detector/non-detectors must be 2-open-distinguished by something other than each other
            for other in self.detector_codes.iter() {
                let mut diff = util::symmetric_diff(&loc.code, &other.1);
                if loc.code.contains(&other.0) {
                    diff -= 1;
                }
                if diff < 2 {
                    return false;
                }
            }
            // non-detectors must be 3-open-distinguished
            for other in self.non_detector_codes.iter() {
                let diff = util::symmetric_diff(&loc.code, other);
                if diff < 3 {
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
                self.detector_codes.push((loc.pos, loc.code));
            }
            else {
                self.non_detector_codes.push(loc.code);
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
    assert!(!s.add(C::new((0, 0), false, vec![])));
    assert!(s.codes.is_empty());
    assert!(!s.add(C::new((0, 0), false, vec![(0, 1)])));
    assert!(s.codes.is_empty());
    
    assert!(s.add(C::new((0, 0), false, vec![(0, 1), (0, 2)])));
    assert_eq!(s.codes.len(), 1);
    assert!(!s.add(C::new((0, 0), false, vec![(0, 1), (0, 2)])));
    assert_eq!(s.codes.len(), 1);

    assert!(!s.add(C::new((0, 0), false, vec![(0, 2), (0, 3)])));
    assert_eq!(s.codes.len(), 1);

    assert!(s.add(C::new((0, 0), false, vec![(0, 3), (0, 4)])));
    assert_eq!(s.codes.len(), 2);

    assert!(!s.add(C::new((0, 0), false, vec![(0, 2), (0, 5)])));
    assert_eq!(s.codes.len(), 2);
    assert!(!s.add(C::new((0, 0), false, vec![(0, 2), (0, 4)])));
    assert_eq!(s.codes.len(), 2);

    assert!(!s.add(C::new((0, 0), false, vec![(0, 3), (0, 4)])));
    assert_eq!(s.codes.len(), 2);
    assert!(!s.add(C::new((0, 0), false, vec![(0, 3), (0, 4), (0, 5)])));
    assert_eq!(s.codes.len(), 2);
    assert!(s.add(C::new((0, 0), false, vec![(0, 3), (0, 4), (0, 5), (0, 6)])));
    assert_eq!(s.codes.len(), 3);

    assert!(s.add(C::new((0, 0), false, vec![(0, 6), (1, 2)])));
    assert_eq!(s.codes.len(), 4);
    assert!(s.add(C::new((0, 0), false, vec![(0, 4), (1, 5), (1, 6)])));
    assert_eq!(s.codes.len(), 5);
}

#[test]
fn test_redld_set() {
    type S = REDLD<i32>;
    type C = <S as Set>::LocatingCode;

    let mut s = S::default();
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, true, vec![])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![0])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![1])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(0, true, vec![1])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(2, true, vec![1])));
    assert_eq!(s.detector_codes.len(), 2);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(3, true, vec![1])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(4, false, vec![20, 21])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(5, false, vec![20, 21])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(5, false, vec![20, 21, 22])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(5, false, vec![20, 22])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(6, true, vec![1, 100])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(!s.add(C::new(20, true, vec![22])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(21, true, vec![20, 23])));
    assert_eq!(s.detector_codes.len(), 5);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(27, true, vec![24])));
    assert_eq!(s.detector_codes.len(), 6);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(!s.add(C::new(40, false, vec![24, 27])));
    assert_eq!(s.detector_codes.len(), 6);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(40, false, vec![24, 27, 28])));
    assert_eq!(s.detector_codes.len(), 6);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(80, true, vec![81])));
    assert_eq!(s.detector_codes.len(), 7);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(!s.add(C::new(82, false, vec![80, 81])));
    assert_eq!(s.detector_codes.len(), 7);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(82, false, vec![81, 84])));
    assert_eq!(s.detector_codes.len(), 7);
    assert_eq!(s.non_detector_codes.len(), 4);
}

#[test]
fn test_detld_set() {
    type S = DETLD<i32>;
    type C = <S as Set>::LocatingCode;

    let mut s = S::default();
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, true, vec![])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);
    
    assert!(!s.add(C::new(0, false, vec![])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![1])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(0, true, vec![1])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, true, vec![1])));
    assert!(!s.add(C::new(0, false, vec![1])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(0, false, vec![2, 3])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(0, true, vec![2, 3])));
    assert!(!s.add(C::new(0, false, vec![2, 3])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(0, false, vec![2, 4])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(0, false, vec![2, 4, 5])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(!s.add(C::new(0, false, vec![1, 6])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(0, false, vec![1, 6, 7])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(0, true, vec![10, 11])));
    assert_eq!(s.detector_codes.len(), 2);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(!s.add(C::new(0, true, vec![3])));
    assert_eq!(s.detector_codes.len(), 2);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(0, true, vec![20])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 3);
}

#[test]
fn test_errld_set() {
    type S = ERRLD<i32>;
    type C = <S as Set>::LocatingCode;

    let mut s = S::default();
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, true, vec![])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, true, vec![1])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![101])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(!s.add(C::new(0, false, vec![101, 102])));
    assert_eq!(s.detector_codes.len(), 0);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(0, true, vec![1, 2])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 0);

    assert!(s.add(C::new(100, false, vec![101, 102, 103])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(3, true, vec![1, 2])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(1, true, vec![0, 2])));
    assert_eq!(s.detector_codes.len(), 1);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(1, true, vec![0, 2, 3])));
    assert_eq!(s.detector_codes.len(), 2);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(4, true, vec![5, 6])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(101, true, vec![102, 103])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(!s.add(C::new(101, true, vec![102, 103, 104])));
    assert_eq!(s.detector_codes.len(), 3);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(101, true, vec![102, 103, 104, 105])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 1);

    assert!(s.add(C::new(200, false, vec![201, 202, 203])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(!s.add(C::new(204, false, vec![201, 202, 203])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(!s.add(C::new(204, false, vec![202, 203, 205])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 2);

    assert!(s.add(C::new(204, false, vec![202, 203, 205, 206])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(!s.add(C::new(50, false, vec![4, 5, 6])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(!s.add(C::new(50, false, vec![4, 5, 6, 7])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 3);

    assert!(s.add(C::new(50, false, vec![4, 5, 6, 7, 8])));
    assert_eq!(s.detector_codes.len(), 4);
    assert_eq!(s.non_detector_codes.len(), 4);

    assert!(s.add(C::new(300, true, vec![301, 302])));
    assert_eq!(s.detector_codes.len(), 5);
    assert_eq!(s.non_detector_codes.len(), 4);

    assert!(!s.add(C::new(310, false, vec![301, 302])));
    assert_eq!(s.detector_codes.len(), 5);
    assert_eq!(s.non_detector_codes.len(), 4);

    assert!(!s.add(C::new(310, false, vec![301, 302, 303])));
    assert_eq!(s.detector_codes.len(), 5);
    assert_eq!(s.non_detector_codes.len(), 4);

    assert!(s.add(C::new(310, false, vec![301, 302, 303, 304])));
    assert_eq!(s.detector_codes.len(), 5);
    assert_eq!(s.non_detector_codes.len(), 5);

    assert!(s.add(C::new(410, false, vec![401, 402, 403, 404])));
    assert_eq!(s.detector_codes.len(), 5);
    assert_eq!(s.non_detector_codes.len(), 6);

    assert!(s.add(C::new(400, true, vec![401, 402])));
    assert_eq!(s.detector_codes.len(), 6);
    assert_eq!(s.non_detector_codes.len(), 6);

    assert!(s.add(C::new(510, false, vec![501, 502, 503])));
    assert_eq!(s.detector_codes.len(), 6);
    assert_eq!(s.non_detector_codes.len(), 7);

    assert!(!s.add(C::new(500, true, vec![501, 502])));
    assert_eq!(s.detector_codes.len(), 6);
    assert_eq!(s.non_detector_codes.len(), 7);

    assert!(s.add(C::new(500, true, vec![501, 502, 520])));
    assert_eq!(s.detector_codes.len(), 7);
    assert_eq!(s.non_detector_codes.len(), 7);
}

#[test]
fn ld_loc_test() {
    type C = LDLOC<i32>;

    assert_eq!(C::new(0, false, vec![1, 2, 3]).dom(), 3);
    assert_eq!(C::new(0, true, vec![1, 2, 3]).dom(), 4);

    assert_eq!(C::new(0, false, vec![1, 2, 3, -1, -2]).dom(), 5);
    assert_eq!(C::new(0, true, vec![1, 2, 3, -1, -2]).dom(), 6);
}

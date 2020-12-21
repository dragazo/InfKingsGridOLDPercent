use std::collections::{BTreeSet, BTreeMap, HashMap, HashSet};
use std::fmt;
use std::io::{self, BufRead, BufReader};
use std::fs::File;
use std::path::Path;
use std::mem;
use std::convert::TryFrom;
use std::str::FromStr;
use std::thread;
use std::sync::{Mutex, Arc};

use itertools::Itertools;
use num::{BigRational, BigInt};
use num::traits::{Zero, One};

#[macro_use]
extern crate more_asserts;

macro_rules! crash {
    ($val:expr) => {
        std::process::exit($val)
    };
    ($val:expr, $($msg:expr),+) => {{
        eprintln!($($msg),+);
        std::process::exit($val);
    }};
}

mod util;
mod adj;
mod codesets;
mod perf;

use adj::AdjacentIterator;
use codesets::LOC;
use perf::{PointMap, PointSet};

enum Goal {
    MeetOrBeat(f64),
    Exactly(usize),
}
impl Goal {
    fn get_value(&self, total_size: usize) -> usize {
        match self {
            Goal::MeetOrBeat(v) => (total_size as f64 * v).floor() as usize,
            Goal::Exactly(v) => *v,
        }
    }
}

trait Solver {
    fn is_old<Adj>(&mut self) -> bool where Adj: adj::AdjacentIterator;
    fn try_satisfy<Adj>(&mut self, goal: Goal) -> Option<usize> where Adj: adj::AdjacentIterator;
}

trait Tessellation: fmt::Display {
    fn size(&self) -> usize;
    fn try_satisfy<Codes, Adj>(&mut self, goal: Goal) -> Option<usize>
    where Codes: codesets::Set<Item = (isize, isize)>, Adj: adj::AdjacentIterator;
}

enum GeometryWithShapeError {
    FileOpenFailure,
    InvalidFormat(&'static str),
}
struct Geometry {
    shape: BTreeSet<(isize, isize)>,
    detectors: BTreeSet<(isize, isize)>,
    w: isize,
    h: isize,
}
impl Geometry {
    fn with_shape(path: &str) -> Result<Self, GeometryWithShapeError> {
        let f = BufReader::new(match File::open(path) {
            Ok(x) => x,
            Err(_) => return Err(GeometryWithShapeError::FileOpenFailure),
        });
        let mut shape: BTreeSet<(isize, isize)> = Default::default();
        for (row, line) in f.lines().map(Result::unwrap).enumerate() {
            for (col, item) in line.split_whitespace().enumerate() {
                match item {
                    x if x.len() != 1 => return Err(GeometryWithShapeError::InvalidFormat("expected geometry element to be length 1")),
                    "." => (),
                    "@" => { shape.insert((row as isize, col as isize)); },
                    _ => return Err(GeometryWithShapeError::InvalidFormat("encountered unexpected character")),
                };
            }
        }
        if shape.is_empty() {
            return Err(GeometryWithShapeError::InvalidFormat("shape is empty"));
        }
        Ok(Geometry::for_printing(&shape, [].iter().copied()))
    }
    fn for_printing<I>(shape: &BTreeSet<(isize, isize)>, detectors: I) -> Self
    where I: Iterator<Item = (isize, isize)>
    {
        assert!(!shape.is_empty());

        let min = (
            shape.iter().map(|(a, _)| *a).min().unwrap(),
            shape.iter().map(|(_, b)| *b).min().unwrap(),
        );
        let max = (
            shape.iter().map(|(a, _)| *a).max().unwrap(),
            shape.iter().map(|(_, b)| *b).max().unwrap(),
        );

        Self {
            shape: shape.iter().map(|p| (p.0 - min.0, p.1 - min.1)).collect(),
            detectors: detectors.map(|p| (p.0 - min.0, p.1 - min.1)).collect(),
            h: max.0 - min.0 + 1,
            w: max.1 - min.1 + 1,
        }
    }
    fn rectangle(rows: usize, cols: usize) -> Self {
        assert!(rows > 0 && cols > 0);
        let shape = (0..rows as isize).flat_map(|r| (0..cols as isize).map(move |c| (r, c))).collect();
        Self {
            shape,
            detectors: Default::default(),
            h: rows as isize,
            w: cols as isize,
        }
    }
    fn width(&self) -> isize {
        self.w
    }
    fn height(&self) -> isize {
        self.h
    }
    fn size(&self) -> usize {
        self.shape.len()
    }
    fn sub_geometries(self, size: usize) -> impl Iterator<Item=Geometry> {
        self.shape.into_iter().combinations(size).map(|set| Geometry::for_printing(&set.into_iter().collect(), [].iter().copied()))
    }
}
impl fmt::Display for Geometry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut working_row = !0;
        let mut working_col = 0;
        for x in &self.shape {
            if x.0 != working_row {
                if working_row != !0 {
                    for _ in 0..(x.0 - working_row) { writeln!(f)?; }
                }
                working_row = x.0;
                working_col = 0;
            }
            for _ in 0..(x.1 - working_col) { write!(f, "  ")?; }
            working_col = x.1 + 1;
            write!(f, "{} ", if self.detectors.contains(x) { 1 } else { 0 })?;
        }
        writeln!(f)?;
        Ok(())
    }
}

type TessellationMap = (HashMap<(isize, isize), (isize, isize)>, (isize, isize), (isize, isize));
struct GeometrySolver<'a, Codes> {
    shape: &'a BTreeSet<(isize, isize)>,
    interior: &'a BTreeSet<(isize, isize)>,
    shape_with_padding: &'a BTreeSet<(isize, isize)>,
    first_per_row: &'a HashSet<(isize, isize)>,
    old_set: &'a mut BTreeSet<(isize, isize)>,
    
    tessellation_maps: &'a [TessellationMap],
    current_tessellation_map: &'a TessellationMap,
    src_basis_a: &'a mut (isize, isize),
    src_basis_b: &'a mut (isize, isize),

    codes: Codes,
    needed: usize,

    classes_to_check: Vec<usize>,
    checked_classes: Vec<usize>,
}
impl<'a, Codes> GeometrySolver<'a, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    fn get_locating_code<Adj: adj::AdjacentIterator>(&self, pos: (isize, isize), offset: (isize, isize)) -> Codes::LocatingCode {
        let mut v = Vec::with_capacity(9);
        let class = Adj::class(pos.0 + offset.0, pos.1 + offset.1); // compute the effective class as if we applied the given offset
        for x in Adj::with_class(pos.0, pos.1, class) {
            if self.old_set.contains(self.current_tessellation_map.0.get(&x).unwrap()) {
                v.push(x);
            }
        }
        let is_detector = self.old_set.contains(self.current_tessellation_map.0.get(&pos).unwrap());
        Codes::LocatingCode::new(pos, is_detector, v)
    }
    fn is_old_interior_up_to<Adj: adj::AdjacentIterator>(&mut self, row: isize) -> bool {
        self.codes.clear();
        for p in self.interior {
            if p.0 >= row - 1 { break; }
            let loc = self.get_locating_code::<Adj>(*p, (0, 0)); // interior uses no offset
            if !self.codes.add(loc) {
                return false;
            }
        }
        true
    }
    fn calc_old_min_interior<'b, Adj, P>(&mut self, mut pos: P) -> bool
    where Adj: adj::AdjacentIterator, P: Iterator<Item = (usize, &'b (isize, isize))> + Clone
    {
        if self.needed == self.old_set.len() {
            return self.is_old::<Adj>();
        } else if let Some((i, &p)) = pos.next() {
            if i + (self.needed - self.old_set.len()) > self.shape.len() {
                return false;
            }

            let good_so_far = !self.first_per_row.contains(&p) || self.is_old_interior_up_to::<Adj>(p.0);
            if !good_so_far {
                return false;
            }

            self.old_set.insert(p);
            if self.calc_old_min_interior::<Adj, _>(pos.clone()) {
                return true;
            }
            self.old_set.remove(&p);
            return self.calc_old_min_interior::<Adj, _>(pos);
        }

        false
    }
}
impl<Codes> Solver for GeometrySolver<'_, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    fn is_old<Adj: adj::AdjacentIterator>(&mut self) -> bool {
        'next_tess: for tess in self.tessellation_maps {
            self.current_tessellation_map = tess;

            // check for validity in all induced classes, including the native one (class 0)
            self.classes_to_check.clear();
            self.checked_classes.clear();
            self.classes_to_check.push(0);
            while let Some(class) = self.classes_to_check.pop() {
                self.checked_classes.push(class);
                let c = Adj::CLASSES[class]; // for an effective offset (center), we can just use the class position itself

                // check validity for this class - on failure move on to the next tessellation
                self.codes.clear();
                for pos in self.shape_with_padding {
                    let loc = self.get_locating_code::<Adj>(*pos, c); // generate loc codes for this class
                    if !self.codes.add(loc) {
                        continue 'next_tess;
                    }
                }

                // compute the induced classes from the current tessellation basis vectors
                let b1 = tess.1;
                let b2 = tess.2;
                for &induced_class in &[Adj::class(c.0 + b1.0, c.1 + b1.1), Adj::class(c.0 + b2.0, c.1 + b2.1)] {
                    // if we haven't seen it before, add it to the list of classes to check
                    if !self.classes_to_check.contains(&induced_class) && !self.checked_classes.contains(&induced_class) {
                        self.classes_to_check.push(induced_class);
                    }
                }
            }

            // merciful domi, we've done it! update the source basis vecs before returning the good news
            *self.src_basis_a = tess.1;
            *self.src_basis_b = tess.2;
            return true;
        }
        false // otherwise no tessellation worked - failure
    }
    fn try_satisfy<Adj: adj::AdjacentIterator>(&mut self, goal: Goal) -> Option<usize> {
        assert_eq!(Adj::CLASSES[0], (0, 0)); // for the love of all that's holy let class 0 be an identity

        self.old_set.clear();
        self.needed = goal.get_value(self.shape.len());

        if self.calc_old_min_interior::<Adj, _>(self.shape.iter().enumerate()) { Some(self.needed) } else { None }
    }
}

#[derive(Debug)]
enum TessellationFailure {
    NoValidTessellations,
}
struct GeometryTessellation {
    geo: Geometry,
    interior: BTreeSet<(isize, isize)>,
    shape_with_padding: BTreeSet<(isize, isize)>,
    first_per_row: HashSet<(isize, isize)>,
    tessellation_maps: Vec<TessellationMap>,
    basis_a: (isize, isize),
    basis_b: (isize, isize),
}
impl fmt::Display for GeometryTessellation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", self.geo)?;
        writeln!(f, "basis: {:?} {:?}", self.basis_a, self.basis_b)?;
        writeln!(f, "size: {}", self.size())?;
        Ok(())
    }
}
impl GeometryTessellation {
    fn solver<Codes>(&mut self) -> GeometrySolver<'_, Codes>
    where Codes: codesets::Set<Item = (isize, isize)>
    {
        GeometrySolver::<Codes> {
            shape: &self.geo.shape,
            interior: &self.interior,
            shape_with_padding: &self.shape_with_padding,
            first_per_row: &self.first_per_row,
            old_set: &mut self.geo.detectors,
            
            tessellation_maps: &self.tessellation_maps,
            current_tessellation_map: &self.tessellation_maps[0],
            src_basis_a: &mut self.basis_a,
            src_basis_b: &mut self.basis_b,

            codes: Default::default(),
            needed: 0,

            classes_to_check: Vec::with_capacity(8),
            checked_classes: Vec::with_capacity(8),
        }
    }
}
impl TryFrom<Geometry> for GeometryTessellation {
    type Error = TessellationFailure;
    fn try_from(geo: Geometry) -> Result<Self, Self::Error> {
        let interior: BTreeSet<_> = geo.shape.iter().filter(|&x| adj::OpenKing::at(*x).all(|p| geo.shape.contains(&p))).copied().collect();
        let first_per_row = {
            let mut s: HashSet<(isize, isize)> = Default::default();
            let mut r = !0;
            for p in geo.shape.iter() {
                if p.0 != r {
                    r = p.0;
                    s.insert(*p);
                }
            }
            s
        };

        let shape_with_padding: BTreeSet<_> = {
            let mut t = geo.shape.clone();
            t.extend(geo.shape.iter().flat_map(|x| adj::OpenKing::at(*x)));
            t
        };
        let shape_with_extra_padding: BTreeSet<_> = {
            let mut t = shape_with_padding.clone();
            t.extend(shape_with_padding.iter().flat_map(|x| adj::OpenKing::at(*x)));
            t
        };

        let tessellation_maps: Vec<_> = {
            let mut valid_tessellations: BTreeMap<BTreeMap<(isize, isize), (isize, isize)>, ((isize, isize), (isize, isize))> = Default::default();
            let mut p: HashSet<(isize, isize)> = HashSet::with_capacity(geo.shape.len() * 25);
            let mut m: BTreeMap<(isize, isize), (isize, isize)> = Default::default();
            
            // needs to be 2w and 2h so that we allow them to slip between one another
            let basis_vecs: Vec<_> = (0..=2*geo.height()).flat_map(|r| (0..=2*geo.width()).map(move |c| (r, c))).collect();
            for basis_a in basis_vecs.iter() {
                'next_basis: for basis_b in basis_vecs.iter() {
                    // clear the caches
                    p.clear();
                    m.clear();

                    // attempt the tessellation
                    for &to in geo.shape.iter() {
                        for i in -3..=3 {
                            for j in -3..=3 {
                                let from = (to.0 + basis_a.0 * i + basis_b.0 * j, to.1 + basis_a.1 * i + basis_b.1 * j);
                                if !p.insert(from) {
                                    continue 'next_basis; // on overlap, this is no good - on to the next
                                }
                                if shape_with_extra_padding.contains(&from) {
                                    m.insert(from, to);
                                }
                            }
                        }
                    }
                    if m.len() != shape_with_extra_padding.len() {
                        continue 'next_basis; // if tessellation is not dense, this is no good - on to the next
                    }

                    // we get to this point then tessellation is ok - add it - if we already had it, keep the old one
                    valid_tessellations.entry(mem::take(&mut m)).or_insert((*basis_a, *basis_b));
                }
            }
            if valid_tessellations.is_empty() {
                return Err(TessellationFailure::NoValidTessellations);
            }
            valid_tessellations.into_iter().map(|(a, (b, c))| (a.into_iter().collect(), b, c)).collect()
        };
        let first_basis_a = tessellation_maps[0].1; // the specific values don't really matter, but better to at least use real values
        let first_basis_b = tessellation_maps[0].2;

        Ok(Self {
            geo, interior, shape_with_padding, tessellation_maps, first_per_row,
            basis_a: first_basis_a,
            basis_b: first_basis_b,
        })
    }
}
impl Tessellation for GeometryTessellation {
    fn size(&self) -> usize {
        self.geo.shape.len()
    }
    fn try_satisfy<Codes, Adj>(&mut self, goal: Goal) -> Option<usize>
    where Codes: codesets::Set<Item = (isize, isize)>, Adj: adj::AdjacentIterator
    {
        self.solver::<Codes>().try_satisfy::<Adj>(goal)
    }
}

struct ExpansionLands {
    field: Vec<(isize, isize)>,
    total_exterior: Vec<(isize, isize)>,
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum TheoStrategy {
    Trivial,
    Avg,
    Dis,
    DisWeightExcess,
    DisWeightShare,
}
impl Default for TheoStrategy {
    fn default() -> Self {
        TheoStrategy::Trivial
    }
}

type Share = BigRational;

#[derive(PartialEq, Eq)]
enum SearchCommand {
    Continue, Halt,
}

#[derive(PartialEq, PartialOrd, Eq, Ord)]
struct TheoProblem {
    center: (isize, isize),
    share: Share,
    avg_share: Share,
    structure: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MaxShareMode {
    Max,
    MaxOrOverThresh,
}
struct TheoSearcher<'a, 'b, Codes> {
    center: (isize, isize),
    closed_interior: &'a [(isize, isize)], // everything up to radius 2
    exterior: &'a [(isize, isize)], // everything at exactly radius 3
    detectors: &'a mut PointSet,

    expansion_map: &'a PointMap<ExpansionLands>, // maps a neighbor of radius 1 or 2 to its outer points up to radius 2, plus a radius 3 border

    codes: &'a mut Codes,

    thresh: &'a Share,
    pipe: &'a mut Option<&'b mut dyn io::Write>,
    problems: &'a mut BTreeSet<TheoProblem>,
    strategy: TheoStrategy,
}
impl<Codes> TheoSearcher<'_, '_, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    #[must_use]
    fn get_locating_code<Adj>(&self, pos: (isize, isize)) -> Codes::LocatingCode
    where Adj: AdjacentIterator
    {
        let mut v = Vec::with_capacity(9);
        for p in Adj::at(pos) {
            if self.detectors.contains(&p) {
                v.push(p);
            }
        }
        let is_detector = self.detectors.contains(&pos);
        Codes::LocatingCode::new(pos, is_detector, v)
    }
    #[must_use]
    fn is_valid_over<Adj, T>(&mut self, range: T) -> bool
    where Adj: AdjacentIterator, T: Iterator<Item = (isize, isize)>
    {
        self.codes.clear();
        for p in range {
            let loc = self.get_locating_code::<Adj>(p);
            if !self.codes.add(loc) {
                return false;
            }
        }
        true
    }
    #[must_use]
    fn calc_share<Adj, ShareAdj>(&self, pos: (isize, isize)) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        assert!(self.detectors.contains(&pos));

        let mut share = Zero::zero();
        for p in ShareAdj::at(pos) {
            let c = self.get_locating_code::<Adj>(p).dom();
            share += Share::new(One::one(), c.into());
        }
        share
    }
    fn max_simultaneous_problem_neighbors_recursive<Adj, ShareAdj>(&mut self, neighbors: &[(isize, isize)], total_field: &[(isize, isize)], total_exterior: &[(isize, isize)], mut field_pos: std::slice::Iter<(isize, isize)>) -> Option<usize>
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        match field_pos.next() {
            None => {
                // if it's not a valid configuration, don't even bother looking at it (return None to denote illegality)
                for point in total_exterior {
                    self.detectors.insert(*point);
                }
                if !self.is_valid_over::<Adj, _>(self.closed_interior.iter().chain(total_field.iter()).copied()) {
                    return None;
                }
                // otherwise count the number of neighbors with problem shares
                Some(neighbors.iter().filter(|x| self.calc_share::<Adj, ShareAdj>(**x) > *self.thresh).count())
            }
            Some(p) => {
                // perform the recursive field expansion
                self.detectors.insert(*p);
                let a = self.max_simultaneous_problem_neighbors_recursive::<Adj, ShareAdj>(neighbors, total_field, total_exterior, field_pos.clone());
                self.detectors.remove(p);
                let b = self.max_simultaneous_problem_neighbors_recursive::<Adj, ShareAdj>(neighbors, total_field, total_exterior, field_pos.clone());

                // return none if both failed, otherwise return whatever was larger
                match (a, b) {
                    (None, None) => None,
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (Some(a), Some(b)) => Some(a.max(b)),
                }
            }
        }
    }
    fn max_simultaneous_problem_neighbors<Adj, ShareAdj>(&mut self, pos: (isize, isize)) -> usize
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        assert!(self.detectors.contains(&pos));
        let mut non_center_neighbors = Vec::with_capacity(8);
        for neighbor in Adj::Open::at(pos) {
            if neighbor != self.center && self.detectors.contains(&neighbor) {
                non_center_neighbors.push(neighbor);
            }
        }
        if non_center_neighbors.is_empty() {
            return 1; // if there are no non-center neighbors, we just have the one problem (center is assumed to have problem share)
        }

        // gather up all the fields we will have to expand in total
        let bounds = ((self.center.0 - 5, self.center.1 - 5), (self.center.0 + 5, self.center.1 + 5));
        let mut total_field = PointSet::with_bounds(bounds.0, bounds.1);
        let mut total_exterior = PointSet::with_bounds(bounds.0, bounds.1);

        for neighbor in non_center_neighbors.iter() {
            let lands = self.expansion_map.get(neighbor).unwrap();
            total_field.extend(lands.field.iter().copied());
            total_exterior.extend(lands.total_exterior.iter().copied());
        }
        for point in total_field.iter() {
            total_exterior.remove(&point);
        }

        #[cfg(debug)]
        {
            println!("total field:\n{}", Geometry::for_printing(&total_field.iter().collect(), self.detectors.iter()));
            println!("total exterior:\n{}", Geometry::for_printing(&total_exterior.iter().collect(), self.detectors.iter()));
            println!("badditude: {}", total_field.iter().count());
            println!("-------------------------------------");
        }

        // convert sets into vectors for fastitude
        let total_field = total_field.iter().collect::<Vec<_>>();
        let total_exterior = total_exterior.iter().collect::<Vec<_>>();
        
        // we have the center problem (by assumption), plus max of non-center neighbors via recursive expansion
        1 + self.max_simultaneous_problem_neighbors_recursive::<Adj, ShareAdj>(&non_center_neighbors, &total_field, &total_exterior, total_field.iter()).unwrap()
    }
    #[must_use]
    fn calc_max_share_expansion_recursive<Adj, ShareAdj, P>(&mut self, pos: (isize, isize), lands: &ExpansionLands, mut ext_pos: P, mode: MaxShareMode) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match ext_pos.next() {
            None => {
                // if it's an invalid configuration, don't even bother looking at it
                for p in lands.total_exterior.iter() {
                    self.detectors.insert(*p);
                }
                if !self.is_valid_over::<Adj, _>(self.closed_interior.iter().chain(lands.field.iter()).copied()) {
                    return -Share::one(); // return -1 to denote nothing (no share here at all)
                }

                // otherwise return the share
                return self.calc_share::<Adj, ShareAdj>(pos);
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_max_share_expansion_recursive::<Adj, ShareAdj, _>(pos, lands, ext_pos.clone(), mode);
                if mode == MaxShareMode::MaxOrOverThresh && &r1 > self.thresh {
                    return r1; // if > thresh max will be too - short circuit if allowed
                }
                self.detectors.remove(&p);
                let r2 = self.calc_max_share_expansion_recursive::<Adj, ShareAdj, _>(pos, lands, ext_pos, mode);

                // return max share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    // expands around boundary to radius 2, returning the maximum share or some possible share > thresh for short-circuitting.
    // returns -1 if no valid configuration exists.
    #[must_use]
    fn calc_max_share_expansion<Adj, ShareAdj>(&mut self, pos: (isize, isize), mode: MaxShareMode) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        let lands = self.expansion_map.get(&pos).unwrap();

        // go ahead and prepare the total exterior before we start searching so we don't have to do it at every terminal node
        for p in lands.total_exterior.iter() {
            self.detectors.insert(*p);
        }

        // compute the max share recursively
        self.calc_max_share_expansion_recursive::<Adj, ShareAdj, _>(pos, lands, lands.field.iter().copied(), mode)
    }
    #[must_use]
    fn do_averaging<Adj, ShareAdj>(&mut self, center_share: &Share) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        assert_gt!(center_share, &self.thresh); // by hypothesis, center is a problem

        // cache share values since they take forever to compute
        let mut shares: HashMap<(isize, isize), Share> = HashMap::with_capacity(25);
        shares.insert(self.center, center_share.clone());

        // also keep track of averaging candidates
        let mut candidates: Vec<(Share, (isize, isize))> = Default::default();

        // compute the weakest max share mode we need in order to work
        let max_share_mode = match self.strategy {
            TheoStrategy::Trivial => panic!("we shouldn't be here"),
            TheoStrategy::Avg | TheoStrategy::Dis => MaxShareMode::MaxOrOverThresh,
            TheoStrategy::DisWeightExcess | TheoStrategy::DisWeightShare => MaxShareMode::Max,
        };

        // for each neighbor of center which is a detector
        for neighbor in Adj::Open::at(self.center) {
            if !self.detectors.contains(&neighbor) {
                continue;
            }

            // compute max share of neighbor and store in cache
            let share = match self.calc_max_share_expansion::<Adj, ShareAdj>(neighbor, max_share_mode) {
                x if x < Share::zero() => return Share::zero(), // if invalid there were no legal configurations in the first place - return something that will always be <= thresh
                x => x,
            };
            shares.insert(neighbor, share.clone());

            // if this is strictly less than thresh it's an averaging candidate
            if &share < self.thresh {
                candidates.push((share, neighbor));
            }
        }

        // sort averagee/discharge candidates by ascending share (use position to break ties just to guarantee invariant exec order)
        candidates.sort();

        // go through the average/discharge candidates and keep track of working share as we do averaging/discharging
        let mut working_share = center_share.clone();
        'next_candidate: for (share, neighbor) in candidates.iter() {
            // look at each of my adjacent detectors and keep track of how many problems i'm next to
            let mut adj_problems = 0;
            let mut sum_weights = Share::zero(); // this is only updated if using weighted strategy
            for other in Adj::Open::at(*neighbor) {
                if !self.detectors.contains(&other) {
                    continue;
                }

                // compute its max share - use cache for lookups when possible (at this point center and neighbors are in cache, so only misses are boundary points)
                let sh = match shares.entry(other).or_insert_with(|| self.calc_max_share_expansion::<Adj, ShareAdj>(other, max_share_mode)) {
                    x if *x < Share::zero() => return Share::zero(), // if invalid there were no legal configurations in the first place - return something that will always be <= thresh
                    x => x,
                };

                // if this is strictly larger than thresh it's a problem
                if &*sh > self.thresh {
                    adj_problems += 1; // mark as a problem

                    // do any extra needed work for whatever strategy we're using
                    match self.strategy {
                        TheoStrategy::Trivial => panic!("we shouldn't be here"),
                        TheoStrategy::Avg => if adj_problems > 1 { continue 'next_candidate; } // averaging is discharging that requires adj_problems == 1
                        TheoStrategy::Dis => (),                                               // discharge has no other requirements
                        TheoStrategy::DisWeightExcess => sum_weights += &*sh - self.thresh,    // weighted discharging with excess
                        TheoStrategy::DisWeightShare => sum_weights += &*sh,                   // weighted discharging with share
                    }
                }
            }
            assert_ne!(adj_problems, 0); // this should never be zero because by hypothesis center itself is a problem

            // compute the total amount of safe discharge
            let max_safe_discharge = {
                let pool = self.thresh - share; // the total amount of share this neighbor can accept
                match self.strategy {
                    TheoStrategy::Trivial => panic!("we shouldn't be here"),
                    TheoStrategy::Avg | TheoStrategy::Dis => pool / Share::from_integer(adj_problems.into()), // same logic due to above
                    TheoStrategy::DisWeightExcess => pool * ((center_share - self.thresh) / sum_weights),     // same logic as avg/dis, except weighted by excess
                    TheoStrategy::DisWeightShare => pool * (center_share / sum_weights),                      // same but different weights
                }
            };
            assert_gt!(max_safe_discharge, Share::zero()); // sanity check

            // apply maximum safe discharging - if we drop down to or below the target thresh, we're done - yay!
            working_share -= max_safe_discharge;
            if &working_share <= self.thresh {
                return working_share;
            }
        }
        // otherwise we failed to correct - discharge still has some hope
        match self.strategy {
            TheoStrategy::Trivial => panic!("we shouldn't be here"),
            TheoStrategy::Avg => (), // this can't do anything better
            TheoStrategy::DisWeightExcess | TheoStrategy::DisWeightShare => (), // these aren't supported for batch discharge source logic yet - probably never will be
            TheoStrategy::Dis => {
                let mut new_working_share = center_share.clone(); // get a new working share

                // go through the candidates again
                for (share, neighbor) in candidates.iter() {
                    let simultaneous_adj_problems = self.max_simultaneous_problem_neighbors::<Adj, ShareAdj>(*neighbor);
                    assert!(simultaneous_adj_problems > 0); // sanity check

                    let dis = (self.thresh - share) / Share::from_integer(simultaneous_adj_problems.into());
                    assert_gt!(dis, Share::zero()); // sanity check

                    new_working_share -= dis;
                    if &new_working_share <= self.thresh {
                        return new_working_share;
                    }
                }

                // at the end we should at least do as well as the non-simultaneous expansion
                assert_le!(new_working_share, working_share);
                working_share = new_working_share; // replace with the better value
            }
        }
        // but if that also failed, just return the best we could do
        working_share
    }
    #[must_use]
    fn calc_recursive<Adj, ShareAdj, P>(&mut self, mut pos: P) -> SearchCommand
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match pos.next() {
            // if we have no positions remaining, check for first order validity
            None => {
                // fill in the exterior
                for p in self.exterior.iter() {
                    self.detectors.insert(*p);
                }
                // if not valid over the ball2 iter field, ignore (invalid configuration)
                if !self.is_valid_over::<Adj, _>(self.closed_interior.iter().copied()) {
                    return SearchCommand::Continue;
                }

                // compute share of center
                let share = self.calc_share::<Adj, ShareAdj>(self.center);
                
                // compute average share - if share is over thresh, attempt to perform averaging if enabled, otherwise just use same value
                let avg_share = {
                    if &share > self.thresh && self.strategy != TheoStrategy::Trivial {
                        let avg = self.do_averaging::<Adj, ShareAdj>(&share);
                        assert_ge!(avg, Share::zero()); // should be valid
                        assert_le!(avg, share); // should never be worse than we started with
                        avg
                    }
                    else {
                        share.clone() 
                    }
                };

                // if it was over thresh, display as problem case
                if &avg_share > self.thresh {
                    // gather up all the info into a problem description
                    let geo = Geometry::for_printing(&self.closed_interior.iter().copied().collect(), self.detectors.iter());
                    let structure = format!("{}", geo);
                    let problem = TheoProblem {
                        center: self.center,
                        share,
                        avg_share,
                        structure,
                    };
                    // add to problems list (automatically sorted like we want)
                    self.problems.insert(problem);

                    match *self.pipe {
                        // if printing enabled, show early warning if this was the first problem (nice since we delay problem printing till end for sorted order)
                        Some(ref mut f) => {
                            if self.problems.len() == 1 {
                                writeln!(f, "encountered problems...\n").unwrap();
                            }
                        }
                        // otherwise we're not interested in the problems, so stop looking for more of them
                        None => return SearchCommand::Halt,
                    }
                }

                return SearchCommand::Continue;
            }
            // otherwise recurse on both branches at this position
            Some(p) => {
                self.detectors.insert(p);
                if self.calc_recursive::<Adj, ShareAdj, _>(pos.clone()) == SearchCommand::Halt {
                    return SearchCommand::Halt;
                }
                self.detectors.remove(&p);
                return self.calc_recursive::<Adj, ShareAdj, _>(pos);
            }
        }
    }
}
#[must_use]
fn calc_lower_bound<Codes, Adj, ShareAdj>(strategy: TheoStrategy, thresh: Share, mut pipe: Option<&mut dyn io::Write>) -> bool
where Codes: codesets::Set<Item = (isize, isize)> + 'static, Adj: AdjacentIterator, ShareAdj: AdjacentIterator
{
    assert_gt!(thresh, Share::zero()); // we require thresh in (0, 1]
    assert_le!(thresh, Share::one());

    let mut closed_interior = PointSet::default(); // everything up to radius 2
    let mut open_interior = PointSet::default();   // everything up to radius 2 except center
    let mut exterior = PointSet::default();        // everything at exactly radius 3
    let mut detectors = PointSet::default();

    let mut expansion_map = PointMap::default();

    let mut codes: Codes = Default::default();
    let mut problems: BTreeSet<TheoProblem> = Default::default();

    // convenience function since PointSet cannot impl FromIterator
    fn collect<I: IntoIterator<Item = (isize, isize)>>(bounds: &((isize, isize), (isize, isize)), iter: I) -> PointSet {
        let mut s = PointSet::with_bounds(bounds.0, bounds.1);
        s.extend(iter);
        s
    };

    let share_thresh = thresh.recip();

    // fold recursive results from all provided center values
    for &center in Adj::CLASSES {
        // set bounds for all the sets/maps we need
        let bounds = ((center.0 - 5, center.1 - 5), (center.0 + 5, center.1 + 5));

        closed_interior.set_bounds(bounds.0, bounds.1);
        open_interior.set_bounds(bounds.0, bounds.1);
        exterior.set_bounds(bounds.0, bounds.1);
        detectors.set_bounds(bounds.0, bounds.1);
    
        expansion_map.set_bounds(bounds.0, bounds.1);
        
        // --------------------------------------------------------------------------------

        // generate closed interior - everything up to radius 2
        closed_interior.clear();
        closed_interior.extend(Adj::Open::at(center).flat_map(Adj::Closed::at));

        #[cfg(debug)]
        println!("closed interior:\n{}", Geometry::for_printing(&closed_interior, &Default::default()));

        // generate open interior - everything up to radius 2 except the center
        open_interior.clone_from(&closed_interior);
        open_interior.remove(&center);

        #[cfg(debug)]
        println!("open interior:\n{}", Geometry::for_printing(&open_interior, &Default::default()));

        // generate exterior - everything at exactly radius 3
        exterior.clear();
        exterior.extend(closed_interior.iter().flat_map(Adj::Open::at).filter(|p| !closed_interior.contains(p)));

        #[cfg(debug)]
        println!("exterior:\n{}", Geometry::for_printing(&exterior, &Default::default()));

        // generate boundary - everything at exactly radius 2
        let boundary = collect(&bounds, exterior.iter().flat_map(Adj::Open::at).filter(|p| closed_interior.contains(p)));

        #[cfg(debug)]
        println!("boundary:\n{}", Geometry::for_printing(&boundary, &Default::default()));

        // clear and repopulate expansion map with neighbors and boundary points
        expansion_map.clear();
        for p in Adj::Open::at(center).chain(boundary.iter()) {
            let ball2 = collect(&bounds, Adj::Open::at(p).flat_map(Adj::Closed::at));
            let ball3 = collect(&bounds, ball2.iter().flat_map(Adj::Closed::at));

            let field = collect(&bounds, ball2.iter().filter(|x| !closed_interior.contains(x)));
            let total_exterior = collect(&bounds, exterior.iter().chain(ball3.iter()).filter(|x| !closed_interior.contains(x) && !field.contains(x)));

            let lands = ExpansionLands {
                field: field.iter().collect(),
                total_exterior: total_exterior.iter().collect(),
            };
            #[cfg(debug)]
            {
                println!("{:?} field:          {:?}", p, lands.field);
                println!("{:?} total_exterior: {:?}", p, lands.total_exterior);
                println!();
            }

            expansion_map.insert(p, lands);
        }

        // each pass starts with no detectors except the center
        detectors.clear();
        detectors.insert(center);

        // generate recursive search object (encodes the borrow contracts for borrowchecker)
        let closed_interior_vec: Vec<_> = closed_interior.iter().collect();
        let exterior_vec: Vec<_> = exterior.iter().collect();
        let mut searcher = TheoSearcher {
            center,
            closed_interior: &closed_interior_vec,
            exterior: &exterior_vec,
            detectors: &mut detectors,

            expansion_map: &expansion_map,

            codes: &mut codes,

            thresh: &share_thresh,
            pipe: &mut pipe,
            problems: &mut problems,
            strategy,
        };

        // perform center folding
        if searcher.calc_recursive::<Adj, ShareAdj, _>(open_interior.iter()) == SearchCommand::Halt {
            break;
        }
    }

    if let Some(f) = pipe {
        // if there were no problems then we've proven thresh works
        if problems.is_empty() {
            // attempt to convert to a floating-point representation
            let float = match thresh.numer().to_string().parse::<f64>() {
                Ok(n) => match thresh.denom().to_string().parse::<f64>() {
                    Ok(d) => (n / d).to_string(),
                    Err(_) => "f64 overflow".to_string(),
                },
                Err(_) => "f64 overflow".to_string(),
            };

            // print results and return what we found
            writeln!(f, "found theo lower bound {} ({})", thresh, float).unwrap();
        }
        // otherwise there were problems - conservatively, all we can say is that it didn't work
        else {
            // print out all the problems we encountered (already in desired print order)
            for p in problems.iter() {
                writeln!(f, "problem: {} ({}) (center {:?})\n{}", p.share, p.avg_share, p.center, p.structure).unwrap();
            }
            writeln!(f, "total problems: {}", problems.len()).unwrap();
        }
    }

    // return true if we succeeded, otherwise false
    problems.is_empty()
}

#[derive(Debug)]
enum AdjType {
    Open, Closed
}

struct FiniteGraphSolver<'a, Codes> {
    verts: &'a [Vertex],
    detectors: &'a mut HashSet<usize>,
    needed: usize,
    codes: Codes,
    adj_type: AdjType,
}
impl<Codes> FiniteGraphSolver<'_, Codes>
where Codes: codesets::Set<Item = usize>
{
    fn get_raw_locating_code(&self, p: usize) -> Vec<usize> {
        let mut v = Vec::with_capacity(9);
        let adj = match self.adj_type {
            AdjType::Open => self.verts[p].open_adj.iter(),
            AdjType::Closed => self.verts[p].closed_adj.iter(),
        };
        for x in adj {
            if self.detectors.contains(x) {
                v.push(*x);
            }
        }
        v
    }
    fn is_old(&mut self) -> bool {
        self.codes.clear();
        for i in 0..self.verts.len() {
            let is_detector = self.detectors.contains(&i);
            let v = self.get_raw_locating_code(i);
            let code = Codes::LocatingCode::new(i, is_detector, v);
            if !self.codes.add(code) {
                return false;
            }
        }
        true
    }
    fn find_solution_recursive(&mut self, pos: usize) -> bool {
        if self.needed == self.detectors.len() {
            if self.is_old() {
                return true;
            }
        }
        else if pos < self.verts.len() {
            self.detectors.insert(pos);
            if self.find_solution_recursive(pos + 1) {
                return true;
            }
            self.detectors.remove(&pos);
            return self.find_solution_recursive(pos + 1);
        }

        false
    }
    fn find_solution(&mut self, n: usize, adj_type: AdjType) -> bool {
        self.detectors.clear();
        self.needed = n;
        self.adj_type = adj_type;
        self.find_solution_recursive(0)
    }
}

enum GraphLoadError {
    FileOpenFailure,
    InvalidFormat(&'static str),
}
struct Vertex {
    label: String,
    open_adj: Vec<usize>,
    closed_adj: Vec<usize>,
}
struct FiniteGraph {
    verts: Vec<Vertex>,
    detectors: HashSet<usize>,
}
impl FiniteGraph {
    fn with_shape<P: AsRef<Path>>(path: P) -> Result<Self, GraphLoadError> {
        let mut f = BufReader::new(match File::open(path) {
            Ok(x) => x,
            Err(_) => return Err(GraphLoadError::FileOpenFailure),
        });

        struct Vertexish {
            label: String,
            adj: BTreeSet<usize>,
        }
        let mut v: Vec<Vertexish> = vec![];
        let mut m: HashMap<String, usize> = Default::default();

        let get_vert = |verts: &mut Vec<Vertexish>, map: &mut HashMap<String, usize>, a: &str| {
            match map.get(a) {
                Some(&p) => p,
                None => {
                    verts.push(Vertexish {
                        label: a.into(),
                        adj: Default::default(),
                    });
                    let p = verts.len() - 1;
                    map.insert(a.into(), p);
                    p
                }
            }
        };
        let mut add_edge = |a: &str, b: &str| {
            let idx_a = get_vert(&mut v, &mut m, a);
            let idx_b = get_vert(&mut v, &mut m, b);
            v[idx_a].adj.insert(idx_b);
            v[idx_b].adj.insert(idx_a);
        };

        let mut s = String::new();
        while { s.clear(); let r = f.read_line(&mut s); r.is_ok() && r.unwrap() != 0 } {
            for tok in s.split_whitespace() {
                let p = match tok.find(':') {
                    Some(x) => x,
                    None => return Err(GraphLoadError::InvalidFormat("encountered token without a ':' separator")),
                };
                let a = tok[..p].trim();
                let b = tok[p+1..].trim();
                if b.find(':').is_some() {
                    return Err(GraphLoadError::InvalidFormat("encoundered token with multiple ':' separators"));
                }
                if a == b {
                    return Err(GraphLoadError::InvalidFormat("encountered reflexive connection"));
                }
                add_edge(a, b);
            }
        }

        let mut verts: Vec<Vertex> = Vec::with_capacity(v.len());
        for (i, mut vert) in v.into_iter().enumerate() {
            let open_adj = vert.adj.iter().copied().collect();
            vert.adj.insert(i);
            let closed_adj = vert.adj.iter().copied().collect();
            verts.push(Vertex {
                label: vert.label,
                open_adj,
                closed_adj,
            });
        }
        Ok(FiniteGraph {
            verts,
            detectors: Default::default(),
        })
    }
    fn solver<Codes>(&mut self) -> FiniteGraphSolver<'_, Codes>
    where Codes: codesets::Set<Item = usize>
    {
        FiniteGraphSolver {
            verts: &self.verts,
            detectors: &mut self.detectors,
            needed: 0,
            codes: Default::default(),
            adj_type: AdjType::Open,
        }
    }
    fn get_solution(&self) -> Vec<&str> {
        let mut v: Vec<&str> = self.detectors.iter().map(|&p| self.verts[p].label.as_str()).collect();
        v.sort();
        v
    }

    fn geometric<T: fmt::Debug, F: Fn(&T, &T) -> bool>(points: &[T], f: &F) -> Self {
        let mut verts = Vec::with_capacity(points.len());
        for (i, a) in points.iter().enumerate() {
            let mut adj = vec![];
            for (j, b) in points[..i].iter().enumerate() {
                if f(a, b) { adj.push(j); }
            }
            for (j, b) in points[i + 1..].iter().enumerate() {
                if f(a, b) { adj.push(i + 1 + j); }
            }
            let open_adj = adj.clone();
            adj.push(i);
            verts.push(Vertex { open_adj, closed_adj: adj, label: format!("{:?}", a) });
        }
        Self { verts, detectors: Default::default() }
    }
    fn path(size: usize) -> Self {
        let mut vert_pos = Vec::with_capacity(size);
        for i in 0..size as isize { vert_pos.push(i); }
        Self::geometric(&vert_pos, &|a, b| (a - b).abs() <= 1)
    }
    fn cycle(size: usize) -> Self {
        let mut g = Self::path(size);
        g.verts[0].open_adj.push(size - 1);
        g.verts[0].closed_adj.push(size - 1);
        g.verts[size - 1].open_adj.push(0);
        g.verts[size - 1].closed_adj.push(0);
        g
    }
    fn ladder(length: usize) -> Self {
        let mut vert_pos = Vec::with_capacity(length * 2);
        for i in 0..length as isize { vert_pos.push((0isize, i)); }
        for i in 0..length as isize { vert_pos.push((1isize, i)); }
        Self::geometric(&vert_pos, &|a, b| (a.0 - b.0).abs() + (a.1 - b.1).abs() <= 1)
    }
    fn complete(size: usize) -> Self {
        let mut vert_pos = Vec::with_capacity(size);
        for i in 0..size as isize { vert_pos.push(i); }
        Self::geometric(&vert_pos, &|_, _| true)
    }
}

fn parse_thresh(v: &str) -> f64 {
    match v.parse::<f64>() {
        Ok(v) if v > 0.0 && v <= 1.0 => v,
        Ok(v) => crash!(2, "thresh {} was outside valid range (0, 1]", v),
        Err(_) => crash!(2, "failed to parse '{}' as float", v),
    }
}
fn parse_exact(v: &str, max: usize) -> usize {
    match v.parse::<usize>() {
        Ok(v) if v <= max => v,
        Ok(v) => crash!(2, "count {} exceeded max {}", v, max),
        Err(_) => crash!(2, "failed to parse '{}' as uint", v),
    }
}
fn parse_thresh_frac(v: &str) -> Share {
    // first try to parse as rational
    match v.parse::<Share>() {
        Ok(v) if v > Share::zero() && v <= Share::one() => v,
        Ok(v) => crash!(2, "thresh {} was outside valid range (0, 1]", v),
        Err(_) => {
            // on failure, if it doesn't start with '0.' it was incorrectly formatted rational
            if !v.starts_with("0.") {
                crash!(2, "failed to parse '{}' as rational", v)
            }
            // otherwise try to parse as exact decimal (0, 1)
            match v[2..].parse::<Share>() {
                Ok(n) if n > Share::zero() => {
                    n / BigRational::from_integer(10.into()).pow(v.len() as i32 - 2)
                }
                _ => crash!(2, "failed to parse '{}' as rational", v),
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Parameter {
    DOM, ODOM,
    EDOM, EODOM,
    LD, REDLD, DETLD, ERRLD,
    IC, REDIC, DETIC, RSPIC, ERRIC,
    OLD, REDOLD, DETOLD, RSPOLD, ERROLD,
}
impl FromStr for Parameter {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.to_lowercase().as_str() {
            "dom" => Parameter::DOM,
            "odom" => Parameter::ODOM,
            "edom" => Parameter::EDOM,
            "eodom" => Parameter::EODOM,
            "ld" => Parameter::LD,
            "red:ld" | "redld" => Parameter::REDLD,
            "det:ld" | "detld" => Parameter::DETLD,
            "err:ld" | "errld" => Parameter::ERRLD,
            "ic" => Parameter::IC,
            "red:ic" | "redic" => Parameter::REDIC,
            "det:ic" | "detic" => Parameter::DETIC,
            "rsp:ic" | "rspic" => Parameter::RSPIC,
            "err:ic" | "erric" => Parameter::ERRIC,
            "old" => Parameter::OLD,
            "red:old" | "redold" => Parameter::REDOLD,
            "det:old" | "detold" => Parameter::DETOLD,
            "rsp:old" | "rspold" => Parameter::RSPOLD,
            "err:old" | "errold" => Parameter::ERROLD,

            _ => return Err(()),
        })
    }
}

#[derive(Debug, Clone, Copy)]
enum Graph {
    K, TRI, SQ, HEX, TMB,
}
impl FromStr for Graph {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.to_lowercase().as_str() {
            "k" | "king" | "kings" => Graph::K,
            "tri" => Graph::TRI,
            "sq" | "square" | "grid" => Graph::SQ,
            "hex" => Graph::HEX,
            "tmb" => Graph::TMB,

            _ => return Err(()),
        })
    }
}

fn tess_helper_calc<T: Tessellation>(tess: &mut T, param: Parameter, graph: Graph, goal: &str) -> Option<usize> {
    macro_rules! calc_thresh {
        ($set:ident, $adj:ident) => {
            tess.try_satisfy::<codesets::$set<(isize, isize)>, adj::$adj>(Goal::MeetOrBeat(parse_thresh(goal)))
        }
    }
    macro_rules! calc_exactly {
        ($set:ident, $adj:ident) => {
            tess.try_satisfy::<codesets::$set<(isize, isize)>, adj::$adj>(Goal::Exactly(parse_exact(goal, tess.size())))
        }
    }
    macro_rules! family {
        ($open:ident, $closed:ident) => {
            match param {
                Parameter::DOM => calc_thresh!(DOM, $closed),
                Parameter::ODOM => calc_thresh!(DOM, $open),
                Parameter::EDOM => calc_exactly!(EDOM, $closed),
                Parameter::EODOM => calc_exactly!(EDOM, $open),
                Parameter::LD => calc_thresh!(LD, $open),
                Parameter::REDLD => calc_thresh!(REDLD, $open),
                Parameter::DETLD => calc_thresh!(DETLD, $open),
                Parameter::ERRLD => calc_thresh!(ERRLD, $open),
                Parameter::IC => calc_thresh!(OLD, $closed),
                Parameter::REDIC => calc_thresh!(RED, $closed),
                Parameter::DETIC => calc_thresh!(DET, $closed),
                Parameter::RSPIC => calc_thresh!(RSP, $closed),
                Parameter::ERRIC => calc_thresh!(ERR, $closed),
                Parameter::OLD => calc_thresh!(OLD, $open),
                Parameter::REDOLD => calc_thresh!(RED, $open),
                Parameter::DETOLD => calc_thresh!(DET, $open),
                Parameter::RSPOLD => calc_thresh!(RSP, $open),
                Parameter::ERROLD => calc_thresh!(ERR, $open),
            }
        }
    }

    match graph {
        Graph::K => family!(OpenKing, ClosedKing),
        Graph::TRI => family!(OpenTri, ClosedTri),
        Graph::SQ => family!(OpenGrid, ClosedGrid),
        Graph::HEX => family!(OpenHex, ClosedHex),
        Graph::TMB => family!(OpenTMB, ClosedTMB),
    }
}
fn tess_helper_print<T: Tessellation>(tess: &T, min: usize) {
    let n = tess.size();
    let d = util::gcd(min, n);
    println!("found a {}/{} ({}) solution:\n{}", (min / d), (n / d), (min as f64 / n as f64), tess);
}
fn tess_helper<T: Tessellation>(mut tess: T, param: &str, graph: &str, goal: &str) {
    let param: Parameter = param.parse().unwrap_or_else(|_| crash!(2, "unknown parameter: {}", param));
    let graph: Graph = graph.parse().unwrap_or_else(|_| crash!(2, "unknown graph: {}", graph));
    
    match tess_helper_calc(&mut tess, param, graph, goal) {
        Some(min) => tess_helper_print(&tess, min),
        None => println!("no solution found"),
    }
}
fn entropy_helper(big_geo: Geometry, entropy_size: &str, param: &str, graph: &str, goal: &str, threadc: &str) {
    let param: Parameter = param.parse().unwrap_or_else(|_| crash!(2, "unknown parameter: {}", param));
    let graph: Graph = graph.parse().unwrap_or_else(|_| crash!(2, "unknown graph: {}", graph));

    let entropy_size = match entropy_size.parse::<usize>() {
        Ok(v) if v <= big_geo.size() => v,
        Ok(v) => crash!(2, "entropy size cannot exceed size of geometry (geo size {}, entropy size {})", big_geo.size(), v),
        Err(_) => crash!(2, "failed to parse '{}' as positive integer", entropy_size),
    };
    let cpus = num_cpus::get();
    let threadc = match threadc.parse::<usize>() {
        Ok(x) if x == 0 => crash!(2, "cannot use 0 threads"),
        Ok(x) if x > cpus => crash!(2, "this system has only {} cores, but {} were requested", cpus, x),
        Ok(x) => x,
        Err(_) => crash!(2, "failed to parse '{}' as positive integer", threadc),
    };

    let geos = big_geo.sub_geometries(entropy_size);
    let done_geos: BTreeSet<_> = Default::default();
    let data = Arc::new(Mutex::new((geos, done_geos, false))); // shared sync state for search
    let goal = Arc::new(goal.to_owned()); // we need to own goal to share, using Arc to avoid multiple copies

    let mut threads: Vec<_> = Vec::with_capacity(threadc);
    for _ in 0..threadc {
        let data = data.clone();
        let goal = goal.clone();
        threads.push(thread::spawn(move || {
            loop {
                let geo = {
                    let mut data = data.lock().unwrap();
                    if data.2 {
                        break // if the solution flag was set, abort
                    }
                    match data.0.next() {
                        Some(geo) => {
                            if !data.1.insert(geo.to_string()) {
                                continue // if we've already seen a similar shape, skip it
                            }
                            geo
                        },
                        None => break, // if there are no more geometries we're done
                    }
                };

                // generate the tessellation structure
                let mut tess = match GeometryTessellation::try_from(geo) {
                    Ok(t) => t,
                    Err(_) => continue, // on tessellation failure, just move on to next geometry
                };

                // on successful search, print result and terminate
                if let Some(min) = tess_helper_calc(&mut tess, param, graph, &goal) {
                    let mut data = data.lock().unwrap();

                    // if solution flag has not been set, print solution and set it
                    if !data.2 {
                        tess_helper_print(&tess, min);
                        data.2 = true;
                    }
                    break;
                }
            }
        }));
    }
    for thread in threads {
        thread.join().unwrap();
    }
    let mut data = data.lock().unwrap(); // we no longer have running threads, so take ownership of the final data

    // if we get to this point and there was no solution then we've exhausted all geometries and found no solutions
    if !data.2 {
        assert!(data.0.next().is_none()); // we should have processed all subgeometries
        println!("no solution found (tested {} geometries)", data.1.len());
    }
}
fn theo_helper(param: &str, graph: &str, thresh: &str, strategy: TheoStrategy, mut pipe: Option<&mut dyn io::Write>) -> bool {
    let param: Parameter = param.parse().unwrap_or_else(|_| crash!(2, "unknown parameter: {}", param));
    let graph: Graph = graph.parse().unwrap_or_else(|_| crash!(2, "unknown graph: {}", graph));

    let thresh = parse_thresh_frac(thresh);
    if let Some(ref mut f) = pipe {
        writeln!(f, "lower bound for {:?} set on {:?} graph - {:?} thresh {}", param, graph, strategy, thresh).unwrap();
    }

    macro_rules! calc {
        ($set:ident, $adj:ident, $shadj:ident) => {
            calc_lower_bound::<codesets::$set<(isize, isize)>, adj::$adj, adj::$shadj>(strategy, thresh, pipe)
        }
    }
    macro_rules! family {
        ($open:ident, $closed:ident) => {
            match param {
                Parameter::DOM => calc!(DOM, $closed, $closed),
                Parameter::ODOM => calc!(DOM, $open, $open),
                Parameter::EDOM | Parameter::EODOM => crash!(2, "lower bound does not currently support {:?}", param), 
                Parameter::LD => calc!(LD, $open, $closed),       // important: this one uses open adj for loc codes but closed adj for share
                Parameter::REDLD => calc!(REDLD, $open, $closed), // important: this one uses open adj for loc codes but closed adj for share
                Parameter::DETLD => calc!(DETLD, $open, $closed), // important: this one uses open adj for loc codes but closed adj for share
                Parameter::ERRLD => calc!(ERRLD, $open, $closed), // important: this one uses open adj for loc codes but closed adj for share
                Parameter::IC => calc!(OLD, $closed, $closed),
                Parameter::REDIC => calc!(RED, $closed, $closed),
                Parameter::DETIC => calc!(DET, $closed, $closed),
                Parameter::RSPIC => calc!(RSP, $closed, $closed),
                Parameter::ERRIC => calc!(ERR, $closed, $closed),
                Parameter::OLD => calc!(OLD, $open, $open),
                Parameter::REDOLD => calc!(RED, $open, $open),
                Parameter::DETOLD => calc!(DET, $open, $open),
                Parameter::RSPOLD => calc!(RSP, $open, $open),
                Parameter::ERROLD => calc!(ERR, $open, $open),
            }
        }
    }

    match graph {
        Graph::K => family!(OpenKing, ClosedKing),
        Graph::TRI => family!(OpenTri, ClosedTri),
        Graph::SQ => family!(OpenGrid, ClosedGrid),
        Graph::HEX => family!(OpenHex, ClosedHex),
        Graph::TMB => family!(OpenTMB, ClosedTMB),
    }
}
fn auto_theo_helper(set: &str, graph: &str, strategy: TheoStrategy) {
    let two = BigInt::from(2);
    
    // we know the value is in (0, 1], so start a binary search
    let mut low = BigRational::zero();
    let mut high = BigRational::one();
    let mut thresh = &high - &low;
    loop {
        thresh /= &two;
        let mid = (&low + &high) / &two;
        let rat = util::rationalize(&mid, &thresh);
        println!("search space: [{}, {}]\nprediction: {}", low, high, rat);
        if theo_helper(set, graph, &mid.to_string(), strategy, None) {
            low = mid;
        }
        else {
            high = mid;
        }
    }
}
fn finite_helper(mut g: FiniteGraph, param: &str, count: &str) {
    let param: Parameter = param.parse().unwrap_or_else(|_| crash!(2, "unknown parameter: {}", param));
    let count = match count.parse::<usize>() {
        Ok(n) => {
            if n == 0 { crash!(2, "count cannot be zero"); }
            if n > g.verts.len() { crash!(2, "count cannot be larger than graph size"); }
            n
        }
        Err(_) => crash!(2, "failed to parse '{}' as positive integer", count),
    };

    macro_rules! calc {
        ($t:ident, $m:ident) => {
            g.solver::<codesets::$t<usize>>().find_solution(count, AdjType::$m)
        }
    }

    let success = match param {
        Parameter::DOM => calc!(DOM, Closed),
        Parameter::ODOM => calc!(DOM, Open),
        Parameter::EDOM => calc!(EDOM, Closed),
        Parameter::EODOM => calc!(EDOM, Open),
        Parameter::LD => calc!(LD, Open),
        Parameter::REDLD => calc!(REDLD, Open),
        Parameter::DETLD => calc!(DETLD, Open),
        Parameter::ERRLD => calc!(ERRLD, Open),
        Parameter::IC => calc!(OLD, Closed),
        Parameter::REDIC => calc!(RED, Closed),
        Parameter::DETIC => calc!(DET, Closed),
        Parameter::RSPIC => calc!(RSP, Closed),
        Parameter::ERRIC => calc!(ERR, Closed),
        Parameter::OLD => calc!(OLD, Open),
        Parameter::REDOLD => calc!(RED, Open),
        Parameter::DETOLD => calc!(DET, Open),
        Parameter::RSPOLD => calc!(RSP, Open),
        Parameter::ERROLD => calc!(ERR, Open),
    };
    if success {
        println!("found solution:\n{:?}", g.get_solution());
    }
    else {
        println!("no solution found");
    }
}
fn smallest_helper(param: &str) -> usize {
    let param: Parameter = param.parse().unwrap_or_else(|_| crash!(2, "unknown parameter: {}", param));
    fn test(param: Parameter, mut graph: FiniteGraph, edges: Vec<&Vec<usize>>) -> bool {
        let vertex_count = graph.verts.len();
        macro_rules! calc {
            ($t:ident, $m:ident) => {
                graph.solver::<codesets::$t<usize>>().find_solution(vertex_count, AdjType::$m)
            }
        }
        let success = match param {
            Parameter::DOM => calc!(DOM, Closed),
            Parameter::ODOM => calc!(DOM, Open),
            Parameter::EDOM => unimplemented!(),
            Parameter::EODOM => unimplemented!(),
            Parameter::LD => calc!(LD, Open),
            Parameter::REDLD => calc!(REDLD, Open),
            Parameter::DETLD => calc!(DETLD, Open),
            Parameter::ERRLD => calc!(ERRLD, Open),
            Parameter::IC => calc!(OLD, Closed),
            Parameter::REDIC => calc!(RED, Closed),
            Parameter::DETIC => calc!(DET, Closed),
            Parameter::RSPIC => calc!(RSP, Closed),
            Parameter::ERRIC => calc!(ERR, Closed),
            Parameter::OLD => calc!(OLD, Open),
            Parameter::REDOLD => calc!(RED, Open),
            Parameter::DETOLD => calc!(DET, Open),
            Parameter::RSPOLD => calc!(RSP, Open),
            Parameter::ERROLD => calc!(ERR, Open),
        };
        if success {
            println!("found {} vertex solution with edges:\n{:?}", vertex_count, edges);
        }
        success
    }
    // we have to handle 1 vertex graph separately because following logic does combinations(2), which for a singleton graph is nothing
    let singleton_graph = FiniteGraph { verts: vec![Vertex { label: 0.to_string(), open_adj: vec![], closed_adj: vec![0] }], detectors: Default::default() };
    if test(param, singleton_graph, vec![]) { return 1; }
    for vertex_count in 2.. {
        let complete_edges: Vec<Vec<usize>> = (0..vertex_count).combinations(2).collect();
        for edge_count in 0..=complete_edges.len() {
            for edges in complete_edges.iter().combinations(edge_count) {
                let mut vert_adjs = Vec::with_capacity(vertex_count);
                for _ in 0..vertex_count {
                    vert_adjs.push(Vec::with_capacity(vertex_count));
                }
                for edge in edges.iter() {
                    let (a, b) = (edge[0], edge[1]);
                    debug_assert_ne!(a, b); // sanity check
                    vert_adjs[a].push(b);
                    vert_adjs[b].push(a);
                }
                let verts = vert_adjs.into_iter().enumerate().map(|(i, mut adj)| {
                    let open_adj = adj.clone();
                    adj.push(i);
                    Vertex { label: i.to_string(), open_adj, closed_adj: adj }
                }).collect();
                let graph = FiniteGraph { verts, detectors: Default::default() };
                if test(param, graph, edges) { return vertex_count; }
            }
        }
    }
    panic!();
}
#[test]
fn test_smallest() {
    debug_assert_eq!(smallest_helper("dom"), 1);
    debug_assert_eq!(smallest_helper("odom"), 2);
}

fn parse_positive(v: &str) -> usize {
    match v.parse::<usize>() {
        Ok(v) if v > 0 => v,
        _ => crash!(2, "failed to parse '{}' as positive integer", v),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let parse_dim = |val: &str| {
        match val.parse::<usize>() {
            Ok(v) if v > 0 => v,
            Ok(_) => crash!(2, "dimension cannot be zero"),
            Err(_) => crash!(2, "failed to parse '{}' as positive int", val),
        }
    };
    let get_geometry = |path: &str| {
        match Geometry::with_shape(path) {
            Ok(g) => g,
            Err(e) => match e {
                GeometryWithShapeError::FileOpenFailure => crash!(2, "failed to open tessellation file {}", args[2]),
                GeometryWithShapeError::InvalidFormat(msg) => crash!(2, "file {} was invalid format: {}", args[2], msg),
            }
        }
    };

    match args.get(1).map(String::as_str) {
        Some("finite") => {
            if args.len() != 5 {
                crash!(1, "usage: {} finite [graph-file] [set-type] [set-size]", args[0]);
            }
            let graph_path = &args[2];
            let g = match FiniteGraph::with_shape(graph_path) {
                Ok(g) => g,
                Err(e) => match e {
                    GraphLoadError::FileOpenFailure => crash!(2, "failed to open graph file {}", graph_path),
                    GraphLoadError::InvalidFormat(msg) => crash!(2, "file {} was invalid format: {}", graph_path, msg),
                }
            };
            finite_helper(g, &args[3], &args[4]);
        }
        Some("finite-path") => {
            if args.len() != 5 {
                crash!(1, "usage: {} finite-path [size] [set-type] [set-size]", args[0]);
            }
            let size = parse_positive(&args[2]);
            finite_helper(FiniteGraph::path(size), &args[3], &args[4]);
        }
        Some("finite-cycle") => {
            if args.len() != 5 {
                crash!(1, "usage: {} finite-cycle [size] [set-type] [set-size]", args[0]);
            }
            let size = parse_positive(&args[2]);
            finite_helper(FiniteGraph::cycle(size), &args[3], &args[4]);
        }
        Some("finite-ladder") => {
            if args.len() != 5 {
                crash!(1, "usage: {} finite-ladder [length] [set-type] [set-size]", args[0]);
            }
            let length = parse_positive(&args[2]);
            finite_helper(FiniteGraph::ladder(length), &args[3], &args[4]);
        }
        Some("finite-complete") => {
            if args.len() != 5 {
                crash!(1, "usage: {} finite-complete [size] [set-type] [set-size]", args[0]);
            }
            let size = parse_positive(&args[2]);
            finite_helper(FiniteGraph::complete(size), &args[3], &args[4]);
        }
        Some("smallest") => {
            if args.len() != 3 {
                crash!(1, "usage: {} smallest [set-type]", args[0]);
            }
            smallest_helper(&args[2]);
        }
        Some("auto-theo") => {
            if args.len() != 4 {
                crash!(1, "usage: {} auto-theo [set-type] [graph]", args[0]);
            }
            auto_theo_helper(&args[2], &args[3], TheoStrategy::Trivial);
        }
        Some("auto-theo-avg") => {
            if args.len() != 4 {
                crash!(1, "usage: {} auto-theo-avg [set-type] [graph]", args[0]);
            }
            auto_theo_helper(&args[2], &args[3], TheoStrategy::Avg);
        }
        Some("auto-theo-dis") => {
            if args.len() != 4 {
                crash!(1, "usage: {} auto-theo-dis [set-type] [graph]", args[0]);
            }
            auto_theo_helper(&args[2], &args[3], TheoStrategy::Dis);
        }
        Some("auto-theo-dis-weight-excess") => {
            if args.len() != 4 {
                crash!(1, "usage: {} auto-theo-dis-weight-excess [set-type] [graph]", args[0]);
            }
            auto_theo_helper(&args[2], &args[3], TheoStrategy::DisWeightExcess);
        }
        Some("auto-theo-dis-weight-share") => {
            if args.len() != 4 {
                crash!(1, "usage: {} auto-theo-dis-weight-share [set-type] [graph]", args[0]);
            }
            auto_theo_helper(&args[2], &args[3], TheoStrategy::DisWeightShare);
        }
        Some("theo") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::Trivial, Some(&mut io::stdout()));
        }
        Some("theo-avg") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo-avg [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::Avg, Some(&mut io::stdout()));
        }
        Some("theo-dis") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo-dis [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::Dis, Some(&mut io::stdout()));
        }
        Some("theo-dis-weight-excess") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo-dis-weight-excess [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::DisWeightExcess, Some(&mut io::stdout()));
        }
        Some("theo-dis-weight-share") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo-dis-weight-share [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::DisWeightShare, Some(&mut io::stdout()));
        }
        Some("rect") => {
            if args.len() != 7 {
                crash!(1, "usage: {} rect [rows] [cols] [set-type] [graph] [thresh]", args[0]);
            }
            let rows: usize = parse_dim(&args[2]);
            let cols: usize = parse_dim(&args[3]);
            if rows < 2 || cols < 2 {
                crash!(2, "1xn and nx1 are not supported to avoid branch conditions");
            }
            let tess = GeometryTessellation::try_from(Geometry::rectangle(rows, cols)).unwrap();// RectTessellation::new(rows, cols);
            tess_helper(tess, &args[4], &args[5], &args[6]);
        }
        Some("geo") => {
            if args.len() != 6 {
                crash!(1, "usage: {} geo [geometry-file] [set-type] [graph] [thresh]", args[0]);
            }
            let geo = get_geometry(&args[2]);
            let tess = match GeometryTessellation::try_from(geo) {
                Ok(t) => t,
                Err(e) => {
                    match e {
                        TessellationFailure::NoValidTessellations => crash!(2, "file {} had no valid tessellations", args[2]),
                    }
                }
            };
            println!("loaded geometry: (size {})\n{}\nunique tilings: {}", tess.size(), tess.geo, tess.tessellation_maps.len());
            for (i, (_, a, b)) in tess.tessellation_maps.iter().enumerate() {
                println!("tiling {}: {:?} {:?}", i + 1, a, b);
            }
            println!();
            tess_helper(tess, &args[3], &args[4], &args[5])
        }
        Some("entropy-rect") => {
            if args.len() != 9 {
                crash!(1, "usage: {} entropy-rect [rows] [cols] [entropy-size] [set-type] [graph] [thresh] [threads]", args[0]);
            }
            let rows: usize = parse_dim(&args[2]);
            let cols: usize = parse_dim(&args[3]);
            let big_geo = Geometry::rectangle(rows, cols);
            entropy_helper(big_geo, &args[4], &args[5], &args[6], &args[7], &args[8]);
        }
        Some("entropy-geo") => {
            if args.len() != 8 {
                crash!(1, "usage: {} entropy-geo [geometry-file] [entropy-size] [set-type] [graph] [thresh] [threads]", args[0]);
            }
            let big_geo = get_geometry(&args[2]);
            entropy_helper(big_geo, &args[3], &args[4], &args[5], &args[6], &args[7]);
        }
        _ => crash!(1, "usage: {} [finite|rect|geo|entropy-rect|entropy-geo|theo|theo-avg|theo-dis|auto-theo|auto-theo-avg|auto-theo-dis]", args[0]),
    };
}

#[test]
fn test_theo_hex_works() {
    assert!(theo_helper("ld", "hex", "1/3", TheoStrategy::Dis, None));
    assert!(theo_helper("det:ld", "hex", "3/5", TheoStrategy::Dis, None));
    assert!(theo_helper("red:ic", "hex", "4/7", TheoStrategy::Dis, None));
    assert!(theo_helper("det:ic", "hex", "12/17", TheoStrategy::Dis, None));
    assert!(theo_helper("err:ic", "hex", "5/6", TheoStrategy::Dis, None));
    assert!(theo_helper("old", "hex", "1/2", TheoStrategy::Dis, None));
}

#[test]
fn test_theo_tmb_works() {
    assert!(theo_helper("red:ic", "tmb", "4/9", TheoStrategy::Dis, None));
    assert!(theo_helper("det:ic", "tmb", "3/5", TheoStrategy::Dis, None));
    assert!(theo_helper("err:ic", "tmb", "12/19", TheoStrategy::Dis, None));
    assert!(theo_helper("det:ld", "tmb", "3/5", TheoStrategy::Dis, None));
}
#[test]
fn test_theo_tmb_not_works() {
    assert!(!theo_helper("red:ic", "tmb", "0.44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444445", TheoStrategy::Dis, None));
}
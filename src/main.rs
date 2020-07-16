use std::collections::{BTreeSet, BTreeMap, HashMap, HashSet};
use std::fmt;
use std::io::{self, BufRead, BufReader};
use std::fs::File;
use std::path::Path;
use std::rc::Rc;
use std::cell::RefCell;
use std::mem;
use std::convert::TryFrom;
use itertools::Itertools;
use num::BigRational;
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

use adj::AdjacentIterator;
use codesets::LOC;

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

struct RectSolverBase<'a, Codes> {
    src: &'a mut RectTessellation,
    codes: Codes,
    interior_codes: Codes,
    needed: usize,
    prevs: Vec<(isize, isize)>,
}
struct RectSolver<'a, Codes> {
    base: RectSolverBase<'a, Codes>,
    phases: Vec<(isize, isize)>,
}
impl<Codes> RectSolverBase<'_, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    fn id_to_inside(&self, row: isize, col: isize) -> usize {
        let col_fix = if row < 0 { col - self.src.phase.0 } else if row >= self.src.rows as isize { col + self.src.phase.0 } else { col };
        let row_fix = if col < 0 { row - self.src.phase.1 } else if col >= self.src.cols as isize { row + self.src.phase.1 } else { row };

        let r = (row_fix + 2 * self.src.rows as isize) as usize % self.src.rows;
        let c = (col_fix + 2 * self.src.cols as isize) as usize % self.src.cols;
        r * self.src.cols + c
    }
    fn get_locating_code<Adj>(&self, pos: (isize, isize)) -> Codes::LocatingCode
    where Adj: adj::AdjacentIterator
    {
        let mut v = Vec::with_capacity(9);
        for x in Adj::at(pos) {
            if self.src.old_set[self.id_to_inside(x.0, x.1)] {
                v.push(x)
            }
        }
        let is_detector = self.src.old_set[self.id_to_inside(pos.0, pos.1)];
        Codes::LocatingCode::new(pos, is_detector, v)
    }
    fn is_old_interior_up_to<Adj>(&mut self, row: isize) -> bool
    where Adj: adj::AdjacentIterator
    {
        self.interior_codes.clear();
        for r in 1..row - 1 {
            for c in 1..self.src.cols as isize - 1 {
                let loc = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.add(loc) {
                    return false;
                }
            }
        }
        true
    }
    fn is_old_with_current_phase<Adj>(&mut self) -> bool
    where Adj: adj::AdjacentIterator
    {
        self.codes.clear();
        for &r in &[-1, 0, self.src.rows as isize - 1, self.src.rows as isize] {
            for c in -1 ..= self.src.cols as isize {
                let loc = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.can_add(&loc) || !self.codes.add(loc) {
                    return false;
                }
            }
        }
        for r in 1 ..= self.src.rows as isize - 2 {
            for &c in &[-1, 0, self.src.cols as isize - 1, self.src.cols as isize] {
                let loc = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.can_add(&loc) || !self.codes.add(loc) {
                    return false;
                }
            }
        }
        true
    }
}
impl<Codes> RectSolver<'_, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    fn calc_old_min_interior<Adj>(&mut self, pos: usize) -> bool
    where Adj: adj::AdjacentIterator
    {
        if self.base.needed == self.base.prevs.len() {
            if self.is_old::<Adj>() {
                return true;
            }
        } else if pos + (self.base.needed - self.base.prevs.len()) <= self.base.src.old_set.len() { //pos < self.base.src.old_set.len() {
            let p = ((pos / self.base.src.cols) as isize, (pos % self.base.src.cols) as isize);

            let good_so_far = p.1 != 0 || self.base.is_old_interior_up_to::<Adj>(p.0);

            if good_so_far {
                self.base.src.old_set[pos] = true;
                self.base.prevs.push(p);
                if self.calc_old_min_interior::<Adj>(pos + 1) {
                    return true;
                }
                self.base.prevs.pop();
                self.base.src.old_set[pos] = false;

                return self.calc_old_min_interior::<Adj>(pos + 1);
            }
        }

        false
    }
}
impl<Codes> Solver for RectSolver<'_, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    fn is_old<Adj>(&mut self) -> bool
    where Adj: adj::AdjacentIterator
    {
        if self.base.is_old_interior_up_to::<Adj>(self.base.src.rows as isize) {
            for phase in &self.phases {
                self.base.src.phase = *phase;
                if self.base.is_old_with_current_phase::<Adj>() {
                    return true;
                }
            }
        }
        false
    }
    fn try_satisfy<Adj>(&mut self, goal: Goal) -> Option<usize>
    where Adj: adj::AdjacentIterator
    {
        for x in &mut self.base.src.old_set { *x = false; }
        self.base.prevs.clear();
        self.base.needed = goal.get_value(self.base.src.old_set.len());

        if self.calc_old_min_interior::<Adj>(0) { Some(self.base.needed) } else { None }
    }
}

trait Tessellation: fmt::Display {
    fn size(&self) -> usize;
    fn try_satisfy<Codes, Adj>(&mut self, goal: Goal) -> Option<usize>
    where Codes: codesets::Set<Item = (isize, isize)>, Adj: adj::AdjacentIterator;
}

struct RectTessellation {
    rows: usize,
    cols: usize,
    old_set: Vec<bool>,
    phase: (isize, isize),
}
impl fmt::Display for RectTessellation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for r in 0..self.rows {
            for c in 0..self.cols {
                write!(f, "{} ", if self.old_set[r * self.cols + c] { 1 } else { 0 })?;
            }
            writeln!(f)?;
        }
        writeln!(f, "phase: {:?}", self.phase)?;
        Ok(())
    }
}
impl RectTessellation {
    fn new(rows: usize, cols: usize) -> Self {
        assert_ge!(rows, 2);
        assert_ge!(cols, 2);

        RectTessellation {
            rows, cols,
            old_set: vec![false; rows * cols],
            phase: (0, 0),
        }
    }
    fn solver<Codes>(&mut self) -> RectSolver<'_, Codes>
    where Codes: codesets::Set<Item = (isize, isize)>
    {
        let (r, c) = (self.rows, self.cols);
        RectSolver::<Codes> {
            base: RectSolverBase::<Codes> {
                src: self,
                codes: Default::default(),
                interior_codes: Default::default(),
                needed: 0,
                prevs: vec![],
            },
            phases: {
                let max_phase_x = (r as isize + 1) / 2;
                let max_phase_y = (c as isize + 1) / 2;
                std::iter::once((0, 0)).chain((1..=max_phase_x).map(|x| (x, 0))).chain((1..=max_phase_y).map(|y| (0, y))).collect()
            },
        }
    }
}
impl Tessellation for RectTessellation {
    fn size(&self) -> usize {
        self.old_set.len()
    }
    fn try_satisfy<Codes, Adj>(&mut self, goal: Goal) -> Option<usize>
    where Codes: codesets::Set<Item = (isize, isize)>, Adj: adj::AdjacentIterator
    {
        self.solver::<Codes>().try_satisfy::<Adj>(goal)
    }
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
        Ok(Geometry::for_printing(&shape, &Default::default()))
    }
    fn for_printing(shape: &BTreeSet<(isize, isize)>, detectors: &BTreeSet<(isize, isize)>) -> Self {
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
            detectors: detectors.iter().map(|p| (p.0 - min.0, p.1 - min.1)).collect(),
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
        self.shape.into_iter().combinations(size).map(|set| Geometry::for_printing(&set.into_iter().collect(), &Default::default()))
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

struct GeometrySolver<'a, Codes> {
    shape: &'a BTreeSet<(isize, isize)>,
    interior: &'a BTreeSet<(isize, isize)>,
    shape_with_padding: &'a BTreeSet<(isize, isize)>,
    first_per_row: &'a HashSet<(isize, isize)>,
    old_set: &'a mut BTreeSet<(isize, isize)>,
    
    tessellation_maps: &'a [(HashMap<(isize, isize), (isize, isize)>, (isize, isize), (isize, isize))],
    current_tessellation_map: &'a (HashMap<(isize, isize), (isize, isize)>, (isize, isize), (isize, isize)),
    src_basis_a: &'a mut (isize, isize),
    src_basis_b: &'a mut (isize, isize),

    codes: Codes,
    needed: usize,
}
impl<'a, Codes> GeometrySolver<'a, Codes>
where Codes: codesets::Set<Item = (isize, isize)>
{
    fn get_locating_code<Adj: adj::AdjacentIterator>(&self, pos: (isize, isize)) -> Codes::LocatingCode {
        let mut v = Vec::with_capacity(9);
        for x in Adj::at(pos) {
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
            let loc = self.get_locating_code::<Adj>(*p);
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
            if self.is_old::<Adj>() {
                return true;
            }
        } else if let Some((i, &p)) = pos.next() {
            if i + (self.needed - self.old_set.len()) > self.shape.len() {
                return false;
            }

            let good_so_far = !self.first_per_row.contains(&p) || self.is_old_interior_up_to::<Adj>(p.0);

            if good_so_far {
                self.old_set.insert(p);
                if self.calc_old_min_interior::<Adj, _>(pos.clone()) {
                    return true;
                }
                self.old_set.remove(&p);

                return self.calc_old_min_interior::<Adj, _>(pos);
            }
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

            // check for validity
            self.codes.clear();
            for pos in self.shape_with_padding {
                let loc = self.get_locating_code::<Adj>(*pos);
                if !self.codes.add(loc) {
                    continue 'next_tess; // if this tess had a failure, on to next tess
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
        self.old_set.clear();
        self.needed = goal.get_value(self.shape.len());

        if self.calc_old_min_interior::<Adj, _>(self.shape.iter().enumerate()) { Some(self.needed) } else { None }
    }
}

enum TessellationFailure {
    NoValidTessellations,
}
struct GeometryTessellation {
    geo: Geometry,
    interior: BTreeSet<(isize, isize)>,
    shape_with_padding: BTreeSet<(isize, isize)>,
    first_per_row: HashSet<(isize, isize)>,
    tessellation_maps: Vec<(HashMap<(isize, isize), (isize, isize)>, (isize, isize), (isize, isize))>,
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

#[derive(Default)]
struct BoundaryLands {
    peers: Vec<(isize, isize)>,
    inner_close: Vec<(isize, isize)>,
    outer_close: Vec<(isize, isize)>,
    far: Vec<(isize, isize)>,
}
#[derive(Default)]
struct NeighborLands {
    inner_close: Vec<(isize, isize)>,
    far: Vec<(isize, isize)>,
}

#[derive(Debug, PartialEq)]
enum TheoStrategy {
    NoAveraging,
    AverageWithNeighbors,
    DischargeToNeighbors,
}
impl Default for TheoStrategy {
    fn default() -> Self {
        TheoStrategy::NoAveraging
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

struct TheoSearcher<'a, Codes> {
    center: (isize, isize),
    closed_interior: Rc<RefCell<BTreeSet<(isize, isize)>>>, // everything up to radius 2
    open_interior: Rc<RefCell<BTreeSet<(isize, isize)>>>,   // everything up to radius 2 except center
    detectors: BTreeSet<(isize, isize)>,

    neighbor_map: Rc<RefCell<BTreeMap<(isize, isize), NeighborLands>>>, // maps a neighbor of center (exactly radius 1) to outer points
    boundary_map: Rc<RefCell<BTreeMap<(isize, isize), BoundaryLands>>>, // maps a boundary point (exactly radius 2) to outer points

    codes: Codes,

    thresh: Share,
    pipe: Option<&'a mut dyn io::Write>,
    problems: BTreeSet<TheoProblem>,
    strategy: TheoStrategy,
}
impl<'a, Codes> Default for TheoSearcher<'a, Codes>
where Codes: Default
{
    fn default() -> Self {
        Self {
            center: (0, 0),
            closed_interior: Default::default(),
            open_interior: Default::default(),
            detectors: Default::default(),

            neighbor_map: Default::default(),
            boundary_map: Default::default(),

            codes: Default::default(),

            thresh: Zero::zero(),
            pipe: None,
            problems: Default::default(),
            strategy: TheoStrategy::NoAveraging,
        }
    }
}
impl<'a, Codes> TheoSearcher<'a, Codes>
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
    #[must_use]
    fn calc_max_or_over_thresh_share_boundary_recursive_deep<Adj, ShareAdj, P>(&mut self, pos: (isize, isize), lands: &BoundaryLands, mut far_pos: P) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match far_pos.next() {
            None => {
                // if not valid don't even bother
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center).chain(lands.peers.iter().chain(lands.inner_close.iter()).copied())) {
                    return -Share::one(); // invalid config has no share - return invalid value
                }

                // otherwise return the share
                return self.calc_share::<Adj, ShareAdj>(pos);
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_max_or_over_thresh_share_boundary_recursive_deep::<Adj, ShareAdj, _>(pos, lands, far_pos.clone());
                if r1 > self.thresh {
                    return r1; // if > thresh then max will be to - short circuit
                }
                self.detectors.remove(&p);
                let r2 = self.calc_max_or_over_thresh_share_boundary_recursive_deep::<Adj, ShareAdj, _>(pos, lands, far_pos);

                // return max share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    #[must_use]
    fn calc_max_or_over_thresh_share_boundary_recursive<Adj, ShareAdj, P>(&mut self, pos: (isize, isize), lands: &BoundaryLands, mut ext_pos: P) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match ext_pos.next() {
            None => {
                // if it's not valid don't even bother inspecting further
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center).chain(lands.peers.iter().copied())) {
                    return -Share::one(); // return -1 to denote no share (illegal config)
                }

                // in this case we have a valid config, refer to the deeper logic to get the actual share value
                return self.calc_max_or_over_thresh_share_boundary_recursive_deep::<Adj, ShareAdj, _>(pos, lands, lands.far.iter().copied());
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_max_or_over_thresh_share_boundary_recursive::<Adj, ShareAdj, _>(pos, lands, ext_pos.clone());
                if r1 > self.thresh {
                    return r1; // if > thresh max will be too - short circuit
                }
                self.detectors.remove(&p);
                let r2 = self.calc_max_or_over_thresh_share_boundary_recursive::<Adj, ShareAdj, _>(pos, lands, ext_pos);

                // return max share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    // expands around boundary to radius 2, returning the maximum share or some possible share > thresh for short-circuitting.
    // returns -1 if no valid configuration exists.
    #[must_use]
    fn calc_max_or_over_thresh_share_boundary<Adj, ShareAdj>(&mut self, pos: (isize, isize)) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        let boundary_map = self.boundary_map.clone();
        let boundary_map = boundary_map.borrow();
        let lands = boundary_map.get(&pos).unwrap();

        // compute the max share recursively
        self.calc_max_or_over_thresh_share_boundary_recursive::<Adj, ShareAdj, _>(pos, lands, lands.outer_close.iter().copied())
    }
    #[must_use]
    fn calc_max_or_over_thresh_share_neighbor_recursive<Adj, ShareAdj, P>(&mut self, neighbor: (isize, isize), lands: &NeighborLands, mut ext_pos: P) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match ext_pos.next() {
            None => {
                // if it's an invalid configuration, don't even bother looking at it
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center).chain(lands.inner_close.iter().copied())) {
                    return -Share::one(); // return -1 to denote nothing (no share here at all)
                }
                
                // otherwise return the share
                return self.calc_share::<Adj, ShareAdj>(neighbor);
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_max_or_over_thresh_share_neighbor_recursive::<Adj, ShareAdj, _>(neighbor, lands, ext_pos.clone());
                if r1 > self.thresh {
                    return r1; // if > thresh max will be too - short circuit
                }
                self.detectors.remove(&p);
                let r2 = self.calc_max_or_over_thresh_share_neighbor_recursive::<Adj, ShareAdj, _>(neighbor, lands, ext_pos);

                // return largest share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    // expands around neighbor to radius 2, returning the maximum share.
    // returns -1 if no valid configuration exists.
    #[must_use]
    fn calc_max_or_over_thresh_share_neighbor<Adj, ShareAdj>(&mut self, neighbor: (isize, isize)) -> Share
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        let neighbor_map = self.neighbor_map.clone();
        let neighbor_map = neighbor_map.borrow();
        let lands = neighbor_map.get(&neighbor).unwrap();

        // compute with recursive helper
        self.calc_max_or_over_thresh_share_neighbor_recursive::<Adj, ShareAdj, _>(neighbor, lands, lands.far.iter().copied())
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

        // for each neighbor of center which is a detector
        for neighbor in Adj::Open::at(self.center) {
            if !self.detectors.contains(&neighbor) {
                continue;
            }

            // compute max share of neighbor and store in cache
            let share = match self.calc_max_or_over_thresh_share_neighbor::<Adj, ShareAdj>(neighbor) {
                x if x < Share::zero() => return Share::zero(), // if invalid there were no legal configurations in the first place - return something that will always be <= thresh
                x => x,
            };
            shares.insert(neighbor, share.clone());

            // if this is strictly less than thresh it's an averaging candidate
            if &share < &self.thresh {
                candidates.push((share, neighbor));
            }
        }

        //  sort averagee candidates by ascending share (use position to break ties just to guarantee invariant exec order)
        candidates.sort();

        // go through the average candidates and keep track of working share as we do averaging/discharging
        let mut working_share = center_share.clone();
        'next_candidate: for (share, neighbor) in candidates {
            // look at each of my adjacent detectors and keep track of how many problems i'm next to
            let mut adj_problems = 0;
            for other in Adj::Open::at(neighbor) {
                if !self.detectors.contains(&other) {
                    continue;
                }

                // compute its max share - use cache for lookups when possible (at this point center and neighbors are in cache, so only misses are boundary points)
                let sh = match shares.entry(other).or_insert_with(|| self.calc_max_or_over_thresh_share_boundary::<Adj, ShareAdj>(other)) {
                    x if &*x < &Share::zero() => return Share::zero(), // if invalid there were no legal configurations in the first place - return something that will always be <= thresh
                    x => x,
                };

                // if this is strictly larger than thresh it's a problem
                if &*sh > &self.thresh {
                    adj_problems += 1;

                    // if this exceeds 1 and we're using averaging, stop here
                    if adj_problems > 1 && self.strategy == TheoStrategy::AverageWithNeighbors {
                        continue 'next_candidate;
                    }
                }
            }
            assert_ne!(adj_problems, 0); // this should never be zero because by hypothesis center itself is a problem

            // compute the total amount of safe discharge (we conservatively only allow uniform discharge into any non-problem neighbor)
            let max_safe_discharge = (&self.thresh - &share) / Share::from_integer(adj_problems.into());
            assert_gt!(max_safe_discharge, Share::zero());

            // apply maximum safe discharging - if we drop down to or below the target thresh, we're done - yay!
            working_share -= max_safe_discharge;
            if &working_share <= &self.thresh {
                return working_share;
            }
        }

        // if we get to this point then we didn't have enough to meet thresh - return the best we could do
        return working_share;
    }
    #[must_use]
    fn calc_recursive<Adj, ShareAdj, P>(&mut self, mut pos: P) -> SearchCommand
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match pos.next() {
            // if we have no positions remaining, check for first order validity
            None => {
                // if not valid on first order, ignore
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center)) {
                    return SearchCommand::Continue;
                }

                // compute share of center
                let share = self.calc_share::<Adj, ShareAdj>(self.center);
                
                // compute average share - if share is over thresh, attempt to perform averaging if enabled, otherwise just use same value
                let avg_share = {
                    if &share > &self.thresh && self.strategy != TheoStrategy::NoAveraging {
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
                if &avg_share > &self.thresh {
                    // gather up all the info into a problem description
                    let geo = Geometry::for_printing(&*self.closed_interior.borrow(), &self.detectors);
                    let structure = format!("{}", geo);
                    let problem = TheoProblem {
                        center: self.center,
                        share,
                        avg_share,
                        structure,
                    };
                    // add to problems list (automatically sorted like we want)
                    self.problems.insert(problem);

                    match self.pipe {
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
    #[must_use]
    fn calc<Adj, ShareAdj>(&mut self, strategy: TheoStrategy, thresh: Share, pipe: Option<&'a mut dyn io::Write>) -> bool
    where Adj: AdjacentIterator, ShareAdj: AdjacentIterator
    {
        assert_gt!(thresh, Share::zero()); // we require thresh in (0, 1]
        assert_le!(thresh, Share::one());

        let closed_interior = self.closed_interior.clone();
        let open_interior = self.open_interior.clone();
        let neighbor_map = self.neighbor_map.clone();
        let boundary_map = self.boundary_map.clone();

        // prepare shared search state before starting
        self.thresh = thresh.recip(); // the thresh they tell us is density, but we do everything in terms of share, so invert it
        self.pipe = pipe;
        self.problems.clear();
        self.strategy = strategy;

        // fold recursive results from all provided center values
        for c in Adj::CLASSES {
            // set the center
            self.center = *c;

            // generate closed interior - everything up to radius 2
            {
                let mut closed_interior = closed_interior.borrow_mut();
                closed_interior.clear();
                closed_interior.extend(Adj::Open::at(*c).flat_map(|p| Adj::Closed::at(p)));
            }

            #[cfg(debug)]
            println!("closed interior:\n{}", Geometry::for_printing(&*closed_interior.borrow(), &Default::default()));

            // generate open interior - everything up to radius 2 except the center
            {
                let mut open_interior = open_interior.borrow_mut();
                open_interior.clone_from(&*closed_interior.borrow());
                open_interior.remove(c);
            }

            #[cfg(debug)]
            println!("open interior:\n{}", Geometry::for_printing(&*open_interior.borrow(), &Default::default()));

            // generate exterior - everything at exactly radius 3
            let exterior: BTreeSet<_> = {
                let closed_interior = closed_interior.borrow();
                closed_interior.iter().flat_map(|p| Adj::Open::at(*p)).filter(|p| !closed_interior.contains(p)).collect()
            };

            #[cfg(debug)]
            println!("exterior:\n{}", Geometry::for_printing(&exterior, &Default::default()));

            // generate boundary - everything at exactly radius 2
            let boundary: BTreeSet<_> = {
                let closed_interior = closed_interior.borrow();
                exterior.iter().flat_map(|p| Adj::Open::at(*p)).filter(|p| closed_interior.contains(p)).collect()
            };

            #[cfg(debug)]
            println!("boundary:\n{}", Geometry::for_printing(&boundary, &Default::default()));

            // generate farlands - everything at exactly radius 4
            let farlands: BTreeSet<_> = {
                let closed_interior = closed_interior.borrow();
                exterior.iter().flat_map(|p| Adj::Open::at(*p)).filter(|p| !closed_interior.contains(p) && !exterior.contains(p)).collect()
            };

            #[cfg(debug)]
            println!("farlands:\n{}", Geometry::for_printing(&farlands, &Default::default()));

            // generate neighbor map - maps neighbor of center to outer points
            {
                let mut neighbor_map = neighbor_map.borrow_mut();
                neighbor_map.clear();
                for p in Adj::Open::at(*c) {
                    let ball2: BTreeSet<_> = Adj::Open::at(p).flat_map(|x| Adj::Closed::at(x)).collect();

                    let lands = NeighborLands {
                        inner_close: Adj::Open::at(p).filter(|x| boundary.contains(x)).collect(),
                        far: ball2.iter().filter(|&x| exterior.contains(x)).copied().collect(),
                    };
                    #[cfg(debug)]
                    {
                        println!("neighbor {:?} inner_close: {:?}", p, lands.inner_close);
                        println!("neighbor {:?} far:         {:?}", p, lands.far);
                        println!();
                    }

                    neighbor_map.insert(p, lands);
                }
            }

            // generate boundary map - maps interior boundary to farlands intersection within radius 2 of itself
            {
                let mut boundary_map = boundary_map.borrow_mut();
                boundary_map.clear();
                for p in boundary.iter() {
                    let ball2: BTreeSet<_> = Adj::Open::at(*p).flat_map(|x| Adj::Closed::at(x)).collect();
                    let ball3: BTreeSet<_> = ball2.iter().flat_map(|x| Adj::Closed::at(*x)).collect();

                    let lands = BoundaryLands {
                        peers: ball2.iter().filter(|&x| boundary.contains(x)).copied().collect(),
                        inner_close: Adj::Open::at(*p).filter(|x| exterior.contains(x)).collect(),
                        outer_close: ball3.iter().filter(|&x| exterior.contains(x)).copied().collect(),
                        far: ball2.iter().filter(|&x| farlands.contains(x)).copied().collect(),
                    };
                    #[cfg(debug)]
                    {
                        println!("boundary {:?} peers:       {:?}", p, lands.peers);
                        println!("boundary {:?} inner_close: {:?}", p, lands.inner_close);
                        println!("boundary {:?} outer_close: {:?}", p, lands.outer_close);
                        println!("boundary {:?} far:         {:?}", p, lands.far);
                        println!();
                    }
                    boundary_map.insert(*p, lands);
                }
            }

            // each pass starts with no detectors except the center
            self.detectors.clear();
            self.detectors.insert(*c);

            // perform center folding
            if self.calc_recursive::<Adj, ShareAdj, _>(open_interior.borrow().iter().copied()) == SearchCommand::Halt {
                break;
            }
        }

        match self.pipe {
            Some(ref mut f) => {
                // if there were no problems then we've proven thresh works
                if self.problems.is_empty() {
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
                    for p in self.problems.iter() {
                        writeln!(f, "problem: {} ({}) (center {:?})\n{}", p.share, p.avg_share, p.center, p.structure).unwrap();
                    }
                    writeln!(f, "total problems: {}", self.problems.len()).unwrap();
                }
            },
            None => (),
        }

        // return true if we succeeded, otherwise false
        self.problems.is_empty()
    }
    fn new() -> Self {
        Default::default()
    }
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
}

#[test]
fn test_rect_pos() {
    let mut ggg = RectTessellation::new(4, 4);
    let mut gg = ggg.solver::<codesets::OLD<(isize, isize)>>();
    let g = &mut gg.base;

    assert_eq!(g.id_to_inside(0, 0), 0);
    assert_eq!(g.id_to_inside(1, 0), 4);
    assert_eq!(g.id_to_inside(0, 1), 1);
    assert_eq!(g.id_to_inside(2, 1), 9);

    assert_eq!(g.id_to_inside(-1, 0), 12);
    assert_eq!(g.id_to_inside(-1, 2), 14);
    assert_eq!(g.id_to_inside(-1, 4), 12);
    assert_eq!(g.id_to_inside(4, 4), 0);
    assert_eq!(g.id_to_inside(4, 1), 1);
    assert_eq!(g.id_to_inside(4, -1), 3);
    assert_eq!(g.id_to_inside(-1, -1), 15);

    g.src.phase = (1, 0);

    assert_eq!(g.id_to_inside(0, 0), 0);
    assert_eq!(g.id_to_inside(1, 0), 4);
    assert_eq!(g.id_to_inside(0, 1), 1);
    assert_eq!(g.id_to_inside(2, 1), 9);

    assert_eq!(g.id_to_inside(-1, 0), 15);
    assert_eq!(g.id_to_inside(-1, 2), 13);
    assert_eq!(g.id_to_inside(-1, 4), 15);
    assert_eq!(g.id_to_inside(4, 4), 1);
    assert_eq!(g.id_to_inside(4, 1), 2);
    assert_eq!(g.id_to_inside(4, -1), 0);
    assert_eq!(g.id_to_inside(-1, -1), 14);

    g.src.phase = (0, 1);

    assert_eq!(g.id_to_inside(0, 0), 0);
    assert_eq!(g.id_to_inside(1, 0), 4);
    assert_eq!(g.id_to_inside(0, 1), 1);
    assert_eq!(g.id_to_inside(2, 1), 9);

    assert_eq!(g.id_to_inside(-1, 0), 12);
    assert_eq!(g.id_to_inside(-1, 2), 14);
    assert_eq!(g.id_to_inside(-1, 4), 0);
    assert_eq!(g.id_to_inside(4, 4), 4);
    assert_eq!(g.id_to_inside(4, 1), 1);
    assert_eq!(g.id_to_inside(4, -1), 15);
    assert_eq!(g.id_to_inside(-1, -1), 11);
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

fn tess_helper_calc<T: Tessellation>(tess: &mut T, set: &str, graph: &str, goal: &str) -> Option<usize> {
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
            match set {
                "dom" => calc_thresh!(DOM, $closed),
                "odom" => calc_thresh!(DOM, $open),
                "edom" => calc_exactly!(EDOM, $closed),
                "eodom" => calc_exactly!(EDOM, $open),
                "ld" => calc_thresh!(LD, $open),
                "red:ld" => calc_thresh!(REDLD, $open),
                "det:ld" => calc_thresh!(DETLD, $open),
                "ic" => calc_thresh!(OLD, $closed),
                "red:ic" => calc_thresh!(RED, $closed),
                "det:ic" => calc_thresh!(DET, $closed),
                "err:ic" => calc_thresh!(ERR, $closed),
                "old" => calc_thresh!(OLD, $open),
                "red:old" => calc_thresh!(RED, $open),
                "det:old" => calc_thresh!(DET, $open),
                "err:old" => calc_thresh!(ERR, $open),

                _ => crash!(2, "unknown set: {}", set),
            }
        }
    }

    match graph {
        "king" => family!(OpenKing, ClosedKing),
        "tri" => family!(OpenTri, ClosedTri),
        "grid" => family!(OpenGrid, ClosedGrid),
        "hex" => family!(OpenHex, ClosedHex),
        "tmb" => family!(OpenTMB, ClosedTMB),

        _ => crash!(2, "unknown graph: {}", graph),
    }
}
fn tess_helper_print<T: Tessellation>(tess: &T, min: usize) {
    let n = tess.size();
    let d = util::gcd(min, n);
    println!("found a {}/{} ({}) solution:\n{}", (min / d), (n / d), (min as f64 / n as f64), tess);
}
fn tess_helper<T: Tessellation>(mut tess: T, set: &str, graph: &str, goal: &str) {
    match tess_helper_calc(&mut tess, set, graph, goal) {
        Some(min) => tess_helper_print(&tess, min),
        None => println!("no solution found"),
    }
}
fn entropy_helper(big_geo: Geometry, entropy_size: &str, set: &str, graph: &str, goal: &str) {
    let entropy_size = match entropy_size.parse::<usize>() {
        Ok(v) if v <= big_geo.size() => v,
        Ok(v) => crash!(2, "entropy size cannot exceed size of geometry (geo size {}, entropy size {})", big_geo.size(), v),
        Err(_) => crash!(2, "failed to parse '{}' as positive integer", entropy_size),
    };
    let mut done_geos: BTreeSet<_> = Default::default(); // set of geometies we've already tried

    'next_geo: for geo in big_geo.sub_geometries(entropy_size) {
        if !done_geos.insert(geo.to_string()) {
            continue 'next_geo; // if we've already done this geometry, skip to next
        }
        let mut tess = match GeometryTessellation::try_from(geo) {
            Ok(t) => t,
            Err(_) => continue 'next_geo, // on tessellation failure, just move on to next geometry
        };
        match tess_helper_calc(&mut tess, set, graph, goal) {
            Some(min) => {
                tess_helper_print(&tess, min); // on successful search, print result and terminate
                return;
            }
            None => (), // otherwise do nothing
        }
    }
    println!("no solution found"); // if we get to this point then we've exhausted all our entropy and found no solutions
}
fn theo_helper(set: &str, graph: &str, thresh: &str, strategy: TheoStrategy, mut pipe: Option<&mut dyn io::Write>) -> bool {
    let thresh = parse_thresh_frac(thresh);
    match pipe {
        Some(ref mut f) => writeln!(f, "lower bound for {} set on {} graph - {:?} thresh {}", set, graph, strategy, thresh).unwrap(),
        None => (),
    }

    macro_rules! calc {
        ($set:ident, $adj:ident, $shadj:ident) => {
            TheoSearcher::<codesets::$set<(isize, isize)>>::new().calc::<adj::$adj, adj::$shadj>(strategy, thresh, pipe)
        }
    }
    macro_rules! family {
        ($open:ident, $closed:ident) => {
            match set {
                "dom" => calc!(DOM, $closed, $closed),
                "odom" => calc!(DOM, $open, $open),
                "ld" => calc!(LD, $open, $closed), // important: this one uses open adj for loc codes and closed adj for share
                "red:ld" => calc!(REDLD, $open, $closed), // important: this one uses open adj for loc codes and closed adj for share
                "det:ld" => calc!(DETLD, $open, $closed), // important: this one uses open adj for loc codes and closed adj for share
                "ic" => calc!(OLD, $closed, $closed),
                "red:ic" => calc!(RED, $closed, $closed),
                "det:ic" => calc!(DET, $closed, $closed),
                "err:ic" => calc!(ERR, $closed, $closed),
                "old" => calc!(OLD, $open, $open),
                "red:old" => calc!(RED, $open, $open),
                "det:old" => calc!(DET, $open, $open),
                "err:old" => calc!(ERR, $open, $open),
                
                _ => crash!(2, "unknown set: {}", set),
            }
        }
    }

    match graph {
        "king" => family!(OpenKing, ClosedKing),
        "tri" => family!(OpenTri, ClosedTri),
        "grid" => family!(OpenGrid, ClosedGrid),
        "hex" => family!(OpenHex, ClosedHex),
        "tmb" => family!(OpenTMB, ClosedTMB),

        _ => crash!(2, "unknown graph: {}", graph),
    }
}
fn finite_helper(graph_path: &str, set: &str, count: &str) {
    let mut g = match FiniteGraph::with_shape(graph_path) {
        Ok(g) => g,
        Err(e) => {
            match e {
                GraphLoadError::FileOpenFailure => eprintln!("failed to open graph file {}", graph_path),
                GraphLoadError::InvalidFormat(msg) => eprintln!("file {} was invalid format: {}", graph_path, msg),
            }
            crash!(2);
        }
    };
    let count = match count.parse::<usize>() {
        Ok(n) => {
            if n == 0 {
                crash!(2, "count cannot be zero");
            }
            if n > g.verts.len() {
                crash!(2, "count cannot be larger than graph size");
            }
            n
        }
        Err(_) => crash!(2, "failed to parse '{}' as positive integer", count),
    };

    macro_rules! calc {
        ($t:ident, $m:ident) => {
            g.solver::<codesets::$t<usize>>().find_solution(count, AdjType::$m)
        }
    }

    let success = match set {
        "dom" => calc!(DOM, Closed),
        "odom" => calc!(DOM, Open),
        "edom" => calc!(EDOM, Closed),
        "eodom" => calc!(EDOM, Open),
        "ld" => calc!(LD, Open),
        "red:ld" => calc!(REDLD, Open),
        "det:ld" => calc!(DETLD, Open),
        "ic" => calc!(OLD, Closed),
        "red:ic" => calc!(RED, Closed),
        "det:ic" => calc!(DET, Closed),
        "err:ic" => calc!(ERR, Closed),
        "old" => calc!(OLD, Open),
        "red:old" => calc!(RED, Open),
        "det:old" => calc!(DET, Open),
        "err:old" => calc!(ERR, Open),

        _ => crash!(2, "unknown set: {}", set),
    };
    if success {
        println!("found solution:\n{:?}", g.get_solution());
    }
    else {
        println!("no solution found");
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
            finite_helper(&args[2], &args[3], &args[4]);
        }
        Some("theo") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::NoAveraging, Some(&mut io::stdout()));
        }
        Some("theo-avg") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo-avg [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::AverageWithNeighbors, Some(&mut io::stdout()));
        }
        Some("theo-dis") => {
            if args.len() != 5 {
                crash!(1, "usage: {} theo-dis [set-type] [graph] [thresh]", args[0]);
            }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::DischargeToNeighbors, Some(&mut io::stdout()));
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
            let tess = RectTessellation::new(rows, cols);
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
            if args.len() != 8 {
                crash!(1, "usage: {} entropy-rect [rows] [cols] [entropy-size] [set-type] [graph] [thresh]", args[0]);
            }
            let rows: usize = parse_dim(&args[2]);
            let cols: usize = parse_dim(&args[3]);
            let big_geo = Geometry::rectangle(rows, cols);
            entropy_helper(big_geo, &args[4], &args[5], &args[6], &args[7]);
        }
        Some("entropy-geo") => {
            if args.len() != 7 {
                crash!(1, "usage: {} entropy-geo [geometry-file] [entropy-size] [set-type] [graph] [thresh]", args[0]);
            }
            let big_geo = get_geometry(&args[2]);
            entropy_helper(big_geo, &args[3], &args[4], &args[5], &args[6]);
        }
        _ => crash!(1, "usage: {} [finite|rect|geo|theo|theo-avg]", args[0]),
    };
}

#[test]
fn test_theo_hex() {
    assert!(theo_helper("ld", "hex", "1/3", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("ld", "hex", "0.3333333333333333333333333333333333333333333333333333333333333333", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("ld", "hex", "0.3333333333333333333333333333333333333333333333333333333333333334", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("det:ld", "hex", "3/5", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ld", "hex", "0.6", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ld", "hex", "0.599999999999999999999999999999999999999999999999999999999999", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("det:ld", "hex", "0.600000000000000000000000000000000000000000000000000000000001", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("red:ic", "hex", "4/7", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("red:ic", "hex", "0.57142857142857142857142857142857142857142857142857142857", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("red:ic", "hex", "0.57142857142857142857142857142857142857142857142857142858", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("det:ic", "hex", "12/17", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ic", "hex", "0.70588235294117647058823529411764705882352941176470588235", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("det:ic", "hex", "0.70588235294117647058823529411764705882352941176470588236", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("err:ic", "hex", "5/6", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("err:ic", "hex", "0.83333333333333333333333333333333333333333333333333333333", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("err:ic", "hex", "0.83333333333333333333333333333333333333333333333333333334", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("old", "hex", "1/2", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("old", "hex", "0.499999999999999999999999999999999999999999999999999999999999", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("old", "hex", "0.500000000000000000000000000000000000000000000000000000000001", TheoStrategy::DischargeToNeighbors, None));
}

#[test]
fn test_theo_tmb() {
    assert!(theo_helper("red:ic", "tmb", "3/7", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("red:ic", "tmb", "0.42857142857142857142857142857142857142857142857142857142", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("red:ic", "tmb", "0.42857142857142857142857142857142857142857142857142857143", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("det:ic", "tmb", "3/5", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ic", "tmb", "0.6", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ic", "tmb", "0.5999999999999999999999999999999999999999999999999999999999", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("det:ic", "tmb", "0.6000000000000000000000000000000000000000000000000000000001", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("err:ic", "tmb", "12/19", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("err:ic", "tmb", "0.63157894736842105263157894736842105263157894736842105263", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("err:ic", "tmb", "0.63157894736842105263157894736842105263157894736842105264", TheoStrategy::DischargeToNeighbors, None));

    assert!(theo_helper("det:ld", "tmb", "3/5", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ld", "tmb", "0.6", TheoStrategy::DischargeToNeighbors, None));
    assert!(theo_helper("det:ld", "tmb", "0.5999999999999999999999999999999999999999999999999999999999", TheoStrategy::DischargeToNeighbors, None));
    assert!(!theo_helper("det:ld", "tmb", "0.6000000000000000000000000000000000000000000000000000000001", TheoStrategy::DischargeToNeighbors, None));
}

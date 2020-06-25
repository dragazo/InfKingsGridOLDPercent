use std::collections::{BTreeSet, BTreeMap, HashMap, HashSet};
use std::fmt;
use std::io::{self, BufRead, BufReader};
use std::fs::File;
use std::path::Path;
use std::rc::Rc;
use std::cell::RefCell;
use std::cmp;

#[macro_use]
extern crate more_asserts;

mod util;
mod adj;
mod codesets;

use adj::AdjacentIterator;

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
    fn get_locating_code<Adj>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> where Adj: adj::AdjacentIterator;
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
impl<Codes> RectSolverBase<'_, Codes> where Codes: codesets::Set<(isize, isize)> {
    fn id_to_inside(&self, row: isize, col: isize) -> usize {
        let col_fix = if row < 0 { col - self.src.phase.0 } else if row >= self.src.rows as isize { col + self.src.phase.0 } else { col };
        let row_fix = if col < 0 { row - self.src.phase.1 } else if col >= self.src.cols as isize { row + self.src.phase.1 } else { row };

        let r = (row_fix + 2 * self.src.rows as isize) as usize % self.src.rows;
        let c = (col_fix + 2 * self.src.cols as isize) as usize % self.src.cols;
        r * self.src.cols + c
    }
    fn get_locating_code<Adj: adj::AdjacentIterator>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(9);
        for x in Adj::new(pos.0, pos.1) {
            if self.src.old_set[self.id_to_inside(x.0, x.1)] {
                v.push(x)
            }
        }
        v
    }
    fn is_old_interior_up_to<Adj: adj::AdjacentIterator>(&mut self, row: isize) -> bool {
        self.interior_codes.clear();
        for r in 1..row - 1 {
            for c in 1..self.src.cols as isize - 1 {
                let is_detector = self.src.old_set[self.id_to_inside(r, c)];
                let code = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.add(is_detector, code) {
                    return false;
                }
            }
        }
        true
    }
    fn is_old_with_current_phase<Adj: adj::AdjacentIterator>(&mut self) -> bool {
        self.codes.clear();
        for &r in &[-1, 0, self.src.rows as isize - 1, self.src.rows as isize] {
            for c in -1 ..= self.src.cols as isize {
                let is_detector = self.src.old_set[self.id_to_inside(r, c)];
                let code = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.can_add(is_detector, &code) || !self.codes.add(is_detector, code) {
                    return false;
                }
            }
        }
        for r in 1 ..= self.src.rows as isize - 2 {
            for &c in &[-1, 0, self.src.cols as isize - 1, self.src.cols as isize] {
                let is_detector = self.src.old_set[self.id_to_inside(r, c)];
                let code = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.can_add(is_detector, &code) || !self.codes.add(is_detector, code) {
                    return false;
                }
            }
        }
        true
    }
}
impl<Codes> RectSolver<'_, Codes>
where Codes: codesets::Set<(isize, isize)>
{
    fn calc_old_min_interior<Adj: adj::AdjacentIterator>(&mut self, pos: usize) -> bool {
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
where Codes: codesets::Set<(isize, isize)>
{
    fn get_locating_code<Adj: adj::AdjacentIterator>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        self.base.get_locating_code::<Adj>(pos)
    }
    fn is_old<Adj: adj::AdjacentIterator>(&mut self) -> bool {
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
    fn try_satisfy<Adj: adj::AdjacentIterator>(&mut self, goal: Goal) -> Option<usize> {
        for x in &mut self.base.src.old_set { *x = false; }
        self.base.prevs.clear();
        self.base.needed = goal.get_value(self.base.src.old_set.len());

        if self.calc_old_min_interior::<Adj>(0) { Some(self.base.needed) } else { None }
    }
}

trait Tessellation: fmt::Display {
    fn size(&self) -> usize;
    fn try_satisfy<Codes, Adj>(&mut self, goal: Goal) -> Option<usize>
    where Codes: codesets::Set<(isize, isize)>, Adj: adj::AdjacentIterator;
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
    where Codes: codesets::Set<(isize, isize)>
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
    where Codes: codesets::Set<(isize, isize)>, Adj: adj::AdjacentIterator
    {
        self.solver::<Codes>().try_satisfy::<Adj>(goal)
    }
}

struct Geometry {
    shape: BTreeSet<(isize, isize)>,
    detectors: BTreeSet<(isize, isize)>,
}
impl Geometry {
    fn for_printing(shape: &BTreeSet<(isize, isize)>, detectors: &BTreeSet<(isize, isize)>) -> Self {
        let mut min = (isize::MAX, isize::MAX);
        for p in shape {
            if p.0 < min.0 {
                min.0 = p.0;
            }
            if p.1 < min.1 {
                min.1 = p.1;
            }
        }
        Self {
            shape: shape.iter().map(|p| (p.0 - min.0, p.1 - min.1)).collect(),
            detectors: detectors.iter().map(|p| (p.0 - min.0, p.1 - min.1)).collect(),
        }
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

enum GeometryLoadResult {
    FileOpenFailure,
    InvalidFormat(&'static str),
    TessellationFailure(&'static str),
}
struct GeometrySolver<'a, Codes> {
    shape: &'a BTreeSet<(isize, isize)>,
    interior: &'a BTreeSet<(isize, isize)>,
    shape_with_padding: &'a BTreeSet<(isize, isize)>,
    tessellation_map: &'a HashMap<(isize, isize), (isize, isize)>,
    first_per_row: &'a HashSet<(isize, isize)>,
    old_set: &'a mut BTreeSet<(isize, isize)>,

    codes: Codes,
    needed: usize,
}
impl<'a, Codes> GeometrySolver<'a, Codes>
where Codes: codesets::Set<(isize, isize)>
{
    fn is_old_interior_up_to<Adj: adj::AdjacentIterator>(&mut self, row: isize) -> bool {
        self.codes.clear();
        for p in self.interior {
            if p.0 >= row - 1 { break; }
            let is_detector = self.old_set.contains(self.tessellation_map.get(p).unwrap());
            let code = self.get_locating_code::<Adj>(*p);
            if !self.codes.add(is_detector, code) {
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
where Codes: codesets::Set<(isize, isize)>
{
    fn get_locating_code<Adj: adj::AdjacentIterator>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(9);
        for x in Adj::new(pos.0, pos.1) {
            if self.old_set.contains(self.tessellation_map.get(&x).unwrap()) {
                v.push(x);
            }
        }
        v
    }
    fn is_old<Adj: adj::AdjacentIterator>(&mut self) -> bool {
        self.codes.clear();
        for pos in self.shape_with_padding {
            let is_detector = self.old_set.contains(self.tessellation_map.get(pos).unwrap());
            let code = self.get_locating_code::<Adj>(*pos);
            if !self.codes.add(is_detector, code) {
                return false;
            }
        }
        true
    }
    fn try_satisfy<Adj: adj::AdjacentIterator>(&mut self, goal: Goal) -> Option<usize> {
        self.old_set.clear();
        self.needed = goal.get_value(self.shape.len());

        if self.calc_old_min_interior::<Adj, _>(self.shape.iter().enumerate()) { Some(self.needed) } else { None }
    }
}

struct GeometryTessellation {
    geo: Geometry,
    interior: BTreeSet<(isize, isize)>,
    shape_with_padding: BTreeSet<(isize, isize)>,
    tessellation_map: HashMap<(isize, isize), (isize, isize)>,
    first_per_row: HashSet<(isize, isize)>,
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
    fn with_shape<P: AsRef<Path>>(path: P) -> Result<Self, GeometryLoadResult> {
        let mut f = BufReader::new(match File::open(path) {
            Ok(x) => x,
            Err(_) => return Err(GeometryLoadResult::FileOpenFailure),
        });

        let (basis_a, basis_b) = {
            let mut line = String::new();
            f.read_line(&mut line).unwrap();

            let args: Vec<&str> = line.split_whitespace().collect();
            if args.len() != 4 {
                return Err(GeometryLoadResult::InvalidFormat("expected 4 tessellation arguments as top line of file"));
            }
            let mut parsed: Vec<isize> = vec![];
            for arg in args {
                parsed.push(match arg.parse::<isize>() {
                    Ok(x) => x,
                    Err(_) => return Err(GeometryLoadResult::InvalidFormat("failed to parse a tessellation arg as integer")),
                });
            }
            ((parsed[0], parsed[1]), (parsed[2], parsed[3]))
        };

        let geo = {
            let mut shape: BTreeSet<(isize, isize)> = Default::default();
            for (row, line) in f.lines().map(|x| x.unwrap()).enumerate() {
                for (col, item) in line.split_whitespace().enumerate() {
                    match item {
                        x if x.len() != 1 => return Err(GeometryLoadResult::InvalidFormat("expected geometry element to be length 1")),
                        "." => (),
                        _ => { shape.insert((row as isize, col as isize)); },
                    };
                }
            }
            if shape.is_empty() {
                return Err(GeometryLoadResult::InvalidFormat("shape is empty"));
            }
            Geometry::for_printing(&shape, &Default::default())
        };
        let interior = {
            let boundary: BTreeSet<_> = geo.shape.iter().filter(|x| adj::OpenKing::new(x.0, x.1).any(|y| !geo.shape.contains(&y))).cloned().collect();
            &geo.shape - &boundary
        };
        let first_per_row = {
            let mut s: HashSet<(isize, isize)> = Default::default();
            let mut r = !0;
            for p in &geo.shape {
                if p.0 != r {
                    r = p.0;
                    s.insert(*p);
                }
            }
            s
        };

        let shape_with_padding: BTreeSet<_> = {
            let mut t = geo.shape.clone();
            t.extend(geo.shape.iter().flat_map(|x| adj::OpenKing::new(x.0, x.1)));
            t
        };
        let shape_with_extra_padding: BTreeSet<_> = {
            let mut t = shape_with_padding.clone();
            t.extend(shape_with_padding.iter().flat_map(|x| adj::OpenKing::new(x.0, x.1)));
            t
        };

        let tessellation_map = {
            let mut p: HashSet<(isize, isize)> = HashSet::with_capacity(geo.shape.len() * 25);
            let mut m: HashMap<(isize, isize), (isize, isize)> = HashMap::with_capacity(geo.shape.len() * 9);

            for &to in &geo.shape {
                for i in -2..=2 {
                    for j in -2..=2 {
                        let from = (to.0 + basis_a.0 * i + basis_b.0 * j, to.1 + basis_a.1 * i + basis_b.1 * j);
                        if !p.insert(from) {
                            return Err(GeometryLoadResult::TessellationFailure("tessellation resulted in overlap"));
                        }
                        if shape_with_extra_padding.contains(&from) {
                            m.insert(from, to);
                        }
                    }
                }
            }
            for pos in &shape_with_extra_padding {
                if !m.contains_key(pos) {
                    return Err(GeometryLoadResult::TessellationFailure("tessellation is not dense"));
                }
            }

            m
        };

        Ok(Self {
            geo, interior, shape_with_padding, tessellation_map, first_per_row,
            basis_a, basis_b,
        })
    }
    fn solver<Codes>(&mut self) -> GeometrySolver<'_, Codes>
    where Codes: codesets::Set<(isize, isize)>
    {
        GeometrySolver::<Codes> {
            shape: &self.geo.shape,
            interior: &self.interior,
            shape_with_padding: &self.shape_with_padding,
            tessellation_map: &self.tessellation_map,
            first_per_row: &self.first_per_row,
            old_set: &mut self.geo.detectors,

            codes: Default::default(),
            needed: 0,
        }
    }
}
impl Tessellation for GeometryTessellation {
    fn size(&self) -> usize {
        self.geo.shape.len()
    }
    fn try_satisfy<Codes, Adj>(&mut self, goal: Goal) -> Option<usize>
    where Codes: codesets::Set<(isize, isize)>, Adj: adj::AdjacentIterator
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
}
impl Default for TheoStrategy {
    fn default() -> Self {
        TheoStrategy::NoAveraging
    }
}

#[derive(PartialEq, PartialOrd, Eq, Ord)]
struct LowerBoundProblem {
    center: (isize, isize),
    share: ordered_float::OrderedFloat<f64>,
    structure: String,
}

#[derive(Default)]
struct LowerBoundSearcher<'a, Codes>
where Codes: Default
{
    center: (isize, isize),
    closed_interior: Rc<RefCell<BTreeSet<(isize, isize)>>>, // everything up to radius 2
    open_interior: Rc<RefCell<BTreeSet<(isize, isize)>>>,   // everything up to radius 2 except center
    detectors: BTreeSet<(isize, isize)>,

    neighbor_map: Rc<RefCell<BTreeMap<(isize, isize), NeighborLands>>>, // maps a neighbor of center (exactly radius 1) to outer points
    boundary_map: Rc<RefCell<BTreeMap<(isize, isize), BoundaryLands>>>, // maps a boundary point (exactly radius 2) to outer points

    codes: Codes,

    highest: f64,
    thresh: f64,
    pipe: Option<&'a mut dyn io::Write>,
    problems: BTreeSet<LowerBoundProblem>,
    strategy: TheoStrategy,
}
impl<'a, Codes> LowerBoundSearcher<'a, Codes>
where Codes: codesets::Set<(isize, isize)>
{
    fn get_locating_code<Adj>(&self, pos: (isize, isize)) -> Vec<(isize, isize)>
    where Adj: AdjacentIterator
    {
        let mut v = Vec::with_capacity(9);
        for p in Adj::new(pos.0, pos.1) {
            if self.detectors.contains(&p) {
                v.push(p);
            }
        }
        v
    }
    fn get_locating_code_size<Adj>(&self, pos: (isize, isize)) -> usize
    where Adj: AdjacentIterator
    {
        Adj::new(pos.0, pos.1).filter(|p| self.detectors.contains(&p)).count()
    }
    fn is_valid_over<Adj, T>(&mut self, range: T) -> bool
    where Adj: AdjacentIterator, T: Iterator<Item = (isize, isize)>
    {
        self.codes.clear();
        for p in range {
            let is_detector = self.detectors.contains(&p);
            let code = self.get_locating_code::<Adj>(p);
            if !self.codes.add(is_detector, code) {
                return false;
            }
        }
        true
    }
    fn calc_share<Adj>(&self, pos: (isize, isize)) -> f64
    where Adj: AdjacentIterator
    {
        assert!(self.detectors.contains(&pos));

        let mut share = 0.0;
        for p in Adj::new(pos.0, pos.1) {
            let c = cmp::max(self.get_locating_code_size::<Adj>(p), Codes::MIN_DOM);
            share += 1.0 / c as f64;
        }
        share
    }
    fn calc_share_boundary_recursive_deep<Adj, P>(&mut self, pos: (isize, isize), lands: &BoundaryLands, mut far_pos: P) -> f64
    where Adj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match far_pos.next() {
            None => {
                // if not valid don't even bother
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center).chain(lands.peers.iter().chain(lands.inner_close.iter()).copied())) {
                    return -1.0; // invalid config has no share - return invalid value
                }

                // otherwise return the share
                return self.calc_share::<Adj>(pos);
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_share_boundary_recursive_deep::<Adj, _>(pos, lands, far_pos.clone());
                if r1 > self.thresh {
                    return r1; // if > thresh then max will be to - short circuit
                }
                self.detectors.remove(&p);
                let r2 = self.calc_share_boundary_recursive_deep::<Adj, _>(pos, lands, far_pos);

                // return max share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    fn calc_share_boundary_recursive<Adj, P>(&mut self, pos: (isize, isize), lands: &BoundaryLands, mut ext_pos: P) -> f64
    where Adj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match ext_pos.next() {
            None => {
                // if it's not valid don't even bother inspecting further
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center).chain(lands.peers.iter().copied())) {
                    return -1.0; // return -1 to denote no share (illegal config)
                }

                // in this case we have a valid config, refer to the deeper logic to get the actual share value
                return self.calc_share_boundary_recursive_deep::<Adj, _>(pos, lands, lands.far.iter().copied());
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_share_boundary_recursive::<Adj, _>(pos, lands, ext_pos.clone());
                if r1 > self.thresh {
                    return r1; // if > thresh max will be too - short circuit
                }
                self.detectors.remove(&p);
                let r2 = self.calc_share_boundary_recursive::<Adj, _>(pos, lands, ext_pos);

                // return max share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    fn calc_share_boundary<Adj>(&mut self, pos: (isize, isize)) -> f64
    where Adj: AdjacentIterator
    {
        let boundary_map = self.boundary_map.clone();
        let boundary_map = boundary_map.borrow();
        let lands = boundary_map.get(&pos).unwrap();

        // compute the max share recursively
        self.calc_share_boundary_recursive::<Adj, _>(pos, lands, lands.outer_close.iter().copied())
    }
    // checks neighbor for averaging validity - returns x where x is either -1 (impossible config), max share of neighbor (<= thresh), or some undefined value > thresh
    fn calc_share_neighbor_recursive<Adj, P>(&mut self, neighbor: (isize, isize), lands: &NeighborLands, mut ext_pos: P) -> f64
    where Adj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match ext_pos.next() {
            None => {
                // if it's an invalid configuration, don't even bother looking at it
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center).chain(lands.inner_close.iter().copied())) {
                    return -1.0; // return -1 to denote nothing (no share here at all)
                }
                
                // otherwise return the share
                return self.calc_share::<Adj>(neighbor);
            }
            Some(p) => {
                self.detectors.insert(p);
                let r1 = self.calc_share_neighbor_recursive::<Adj, _>(neighbor, lands, ext_pos.clone());
                if r1 > self.thresh {
                    return r1; // > thresh will cause max to be > thresh as well - short circuit
                }
                self.detectors.remove(&p);
                let r2 = self.calc_share_neighbor_recursive::<Adj, _>(neighbor, lands, ext_pos);

                // return largest share found
                return if r1 >= r2 { r1 } else { r2 };
            }
        }
    }
    // returns Some(x) where x is a valid max share of neighbor <= thresh, otherwise None
    fn calc_share_neighbor<Adj>(&mut self, neighbor: (isize, isize)) -> f64
    where Adj: AdjacentIterator
    {
        let neighbor_map = self.neighbor_map.clone();
        let neighbor_map = neighbor_map.borrow();
        let lands = neighbor_map.get(&neighbor).unwrap();

        // compute with recursive helper
        self.calc_share_neighbor_recursive::<Adj, _>(neighbor, lands, lands.far.iter().copied())
    }
    fn can_average<Adj>(&mut self, center_share: f64) -> Option<f64>
    where Adj: AdjacentIterator
    {
        let neighbor_map = self.neighbor_map.clone();
        let neighbor_map = neighbor_map.borrow();

        // get the list of all averagee candidates and their share (default to -1 to denote invalid)
        let mut neighbors: BTreeMap<(isize, isize), f64> = Adj::Open::at(self.center).filter(|p| self.detectors.contains(p)).map(|p| (p, -1.0)).collect();
        let mut averagee_drops: BTreeSet<(isize, isize)> = Default::default();

        // go through the neighbors and find all the valid average candidates
        for neighbor in neighbors.iter_mut() {
            // if this detector neighbor and its detector neighbors which are open neighbors of center are all already dropped, don't even bother
            if Adj::Closed::at(*neighbor.0).filter(|p| neighbor_map.contains_key(&p) && self.detectors.contains(p)).all(|p| averagee_drops.contains(&p)) {
                continue;
            }

            // otherwise find neighbor max share
            match self.calc_share_neighbor::<Adj>(*neighbor.0) {
                x if x.is_nan() || x.is_infinite() => panic!("invalid neighbor share: {}", x),
                x if x < 0.0 => return Some(0.0), // if invalid there were no legal configurations in the first place - return something that will always be <= thresh
                x if x < self.thresh => *neighbor.1 = x, // if strictly less than thresh update map value
                x if x == self.thresh => { averagee_drops.insert(*neighbor.0); }, // if equal to thresh drop ourself but not neighbors (we're not useful but also not problematic)
                _ => averagee_drops.extend(Adj::Closed::at(*neighbor.0)), // if higher than thresh drop ourself and our neighbors (we're problematic)
            }
        }
        // remove all failed candidates
        for x in averagee_drops.into_iter() {
            neighbors.remove(&x);
        }

        // gather up all the valid averagees and sort by ascending share (use position to break ties just to guarantee invariant exec order)
        let mut averagees: Vec<(f64, (isize, isize))> = neighbors.into_iter().map(|(a, b)| (b, a)).collect();
        assert!(averagees.iter().all(|(sh, _)| *sh >= 0.0 && *sh < self.thresh));
        averagees.sort_by(|x, y| x.partial_cmp(y).unwrap());

        // keep a running track of the boundary share results
        let mut tested_boundaries: BTreeMap<(isize, isize), f64> = Default::default();
        
        // go through the averagees and compute running average
        let mut sum = center_share;
        let mut count = 1.0;
        'average_loop: for (sh, p) in averagees.into_iter() {
            // examine all of its boundary points
            for boundary_pos in neighbor_map.get(&p).unwrap().inner_close.iter() {
                // if it's not a detector it's not a problem - doesn't have a share value
                if !self.detectors.contains(boundary_pos) {
                    continue;
                }

                // compute share of boundary point if we haven't already done so
                let boundary_share = *tested_boundaries.entry(*boundary_pos).or_insert_with(|| self.calc_share_boundary::<Adj>(*boundary_pos));
                match boundary_share {
                    x if x.is_nan() || x.is_infinite() => panic!("invalid boundary share: {}", x),
                    x if x < 0.0 => return Some(0.0), // if invalid there were no legal configurations in the first place - return something that will always be <= thresh
                    x if x <= self.thresh => (), // if no larger than thesh then we're ok so far
                    _ => continue 'average_loop, // otherwise larger than thresh, so we can't use this averagee - on to the next
                }
            }

            // if we get to this point then all of p's neighbors are share no larger than thresh, so we can use this for averaging
            sum += sh;
            count += 1.0;

            // if average is now no larger than thresh then we're done
            let avg = sum / count;
            if avg <= self.thresh {
                return Some(avg);
            }
        }

        // if we get to this point then we didn't have enough to get average under thresh - pity we did all that work
        None
    }
    fn calc_recursive<Adj, P>(&mut self, mut pos: P)
    where Adj: AdjacentIterator, P: Iterator<Item = (isize, isize)> + Clone
    {
        match pos.next() {
            // if we have no positions remaining, check for first order validity
            None => {
                // if not valid on first order, ignore
                if !self.is_valid_over::<Adj, _>(Adj::Closed::at(self.center)) {
                    return;
                }

                // compute share of center
                let share = self.calc_share::<Adj>(self.center);
                
                // compute average share - if share is over thresh, attempt to perform averaging, otherwise just use same value
                let avg_share = {
                    if share > self.thresh && self.strategy != TheoStrategy::NoAveraging {
                        match self.can_average::<Adj>(share) {
                            Some(avg) => {
                                assert_ge!(avg, 0.0);
                                assert_le!(avg, self.thresh);
                                avg
                            }
                            None => share,
                        }
                    }
                    else { share }
                };

                // take the max average share
                if self.highest < avg_share {
                    self.highest = avg_share;
                }

                // if it was over thresh, display as problem case
                if avg_share > self.thresh {
                    match self.pipe {
                        Some(ref mut f) => {
                            // gather up all the info into a problem description (we only need to do this if printing is enabled)
                            let geo = Geometry::for_printing(&*self.closed_interior.borrow(), &self.detectors);
                            let structure = format!("{}", geo);
                            let problem = LowerBoundProblem {
                                center: self.center,
                                share: share.into(),
                                structure,
                            };

                            // if there haven't been any problems so far print a message (early problem warnings are nice since we delay printing till end for sorted order)
                            if self.problems.is_empty() {
                                writeln!(f, "encountered problems...\n").unwrap();
                            }

                            // add to problems list (automatically sorted like we want)
                            self.problems.insert(problem);
                        }
                        None => (),
                    }
                }
            }
            // otherwise recurse on both branches at this position
            Some(p) => {
                self.detectors.insert(p);
                self.calc_recursive::<Adj, _>(pos.clone());
                self.detectors.remove(&p);
                self.calc_recursive::<Adj, _>(pos)
            }
        }
    }
    fn calc<Adj>(&mut self, strategy: TheoStrategy, thresh: f64, pipe: Option<&'a mut dyn io::Write>) -> ((usize, usize), f64)
    where Adj: AdjacentIterator
    {
        let closed_interior = self.closed_interior.clone();
        let open_interior = self.open_interior.clone();
        let neighbor_map = self.neighbor_map.clone();
        let boundary_map = self.boundary_map.clone();

        // prepare shared search state before starting
        self.highest = 0.0;
        self.thresh = thresh;
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
            self.calc_recursive::<Adj, _>(open_interior.borrow().iter().copied());
        }

        // if there were problems, print them if printing is enabled - already in sorted order for user convenience
        if !self.problems.is_empty() {
            match self.pipe {
                Some(ref mut f) => {
                    for p in self.problems.iter() {
                        writeln!(f, "problem: {} (center {:?})\n{}", p.share, p.center, p.structure).unwrap();
                    }
                    writeln!(f, "total problems: {}", self.problems.len()).unwrap();
                },
                None => (),
            }
        };

        // lcm(1..=9) = 2520, so multiply and divide by 2520 to create an exact fractional representation
        let v = (self.highest * 2520.0).round() as usize;
        let d = util::gcd(v, 2520);
        ((2520 / d, v / d), 1.0 / self.highest)
    }
    fn new() -> Self {
        Default::default()
    }
}

#[test]
fn test_lower_bound_searcher_sq_old_optimal() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenGrid>(TheoStrategy::AverageWithNeighbors, 2.50001, None);
    assert_lt!(res.1, 0.400001);
    assert_gt!(res.1, 0.399999);
    assert_eq!(res.0, (2, 5)); // we can find exact solution
}
#[test]
fn test_lower_bound_searcher_sq_old_suboptimal() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenGrid>(TheoStrategy::AverageWithNeighbors, 2.49999, None);
    assert_lt!(res.1, 0.400001);
    assert_gt!(res.1, 0.399999);
    assert_eq!(res.0, (2, 5)); // we can find exact solution (no averaging required)
}

#[test]
fn test_lower_bound_searcher_tri_old_optimal() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenTri>(TheoStrategy::AverageWithNeighbors, 3.250001, None);
    assert_lt!(res.1, 0.3076924); // we don't find exact, but must be less than proven lower bound
}
#[test]
fn test_lower_bound_searcher_tri_old_suboptimal() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenTri>(TheoStrategy::AverageWithNeighbors, 3.249999, None);
    assert_lt!(res.1, 0.3076923);
    assert_ne!(res.0, (4, 13)); // averaging is required so this will be suboptimal
}

#[test]
fn test_lower_bound_searcher_tri_det_optimal() {
    let res = LowerBoundSearcher::<codesets::DET<(isize, isize)>>::new().calc::<adj::OpenTri>(TheoStrategy::AverageWithNeighbors, 2.000001, None);
    assert_lt!(res.1, 0.50001);
    assert_gt!(res.1, 0.49999);
    assert_eq!(res.0, (1, 2)); // we can find exact solution
}
#[test]
fn test_lower_bound_searcher_tri_det_suboptimal() {
    let res = LowerBoundSearcher::<codesets::DET<(isize, isize)>>::new().calc::<adj::OpenTri>(TheoStrategy::AverageWithNeighbors, 1.999999, None);
    assert_lt!(res.1, 0.49999);
    assert_ne!(res.0, (1, 2)); // averaging is required so this will be suboptimal
}

#[test]
fn test_lower_bound_searcher_hex_old_high_share() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenHex>(TheoStrategy::AverageWithNeighbors, 1000.0, None);
    assert_lt!(res.1, 0.50001);
    assert_gt!(res.1, 0.49999);
    assert_eq!(res.0, (1, 2)); // we can find exact solution (no averaging required)
}
#[test]
fn test_lower_bound_searcher_hex_old_optimal() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenHex>(TheoStrategy::AverageWithNeighbors, 2.000001, None);
    assert_lt!(res.1, 0.50001);
    assert_gt!(res.1, 0.39999);
    assert_eq!(res.0, (1, 2)); // we can find exact solution (no averaging required)
}
#[test]
fn test_lower_bound_searcher_hex_old_suboptimal() {
    let res = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenHex>(TheoStrategy::AverageWithNeighbors, 1.999999, None);
    assert_lt!(res.1, 0.50001);
    assert_gt!(res.1, 0.49999);
    assert_eq!(res.0, (1, 2)); // we can find exact solution (no averaging required)
}

struct FiniteGraphSolver<'a, Codes> {
    verts: &'a [Vertex],
    detectors: &'a mut HashSet<usize>,
    needed: usize,
    codes: Codes,
}
impl<Codes> FiniteGraphSolver<'_, Codes>
where Codes: codesets::Set<usize>
{
    fn get_locating_code(&self, p: usize) -> Vec<usize> {
        let mut v = Vec::with_capacity(9);
        for x in &self.verts[p].adj {
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
            let code = self.get_locating_code(i);
            if !self.codes.add(is_detector, code) {
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
    fn find_solution(&mut self, n: usize) -> bool {
        self.detectors.clear();
        self.needed = n;
        self.find_solution_recursive(0)
    }
}

enum GraphLoadError {
    FileOpenFailure,
    InvalidFormat(&'static str),
}
struct Vertex {
    label: String,
    adj: Vec<usize>,
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
        for i in v {
            verts.push(Vertex {
                label: i.label,
                adj: i.adj.into_iter().collect(),
            });
        }
        Ok(FiniteGraph {
            verts,
            detectors: Default::default(),
        })
    }
    fn solver<Codes>(&mut self) -> FiniteGraphSolver<'_, Codes>
    where Codes: codesets::Set<usize>
    {
        FiniteGraphSolver {
            verts: &self.verts,
            detectors: &mut self.detectors,
            needed: 0,
            codes: Default::default(),
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
        Ok(v) => {
            eprintln!("thresh {} was outside valid range (0, 1]", v);
            std::process::exit(7);
        }
        Err(_) => {
            eprintln!("failed to parse '{}' as float", v);
            std::process::exit(7);
        }
    }
}
fn parse_exact(v: &str, max: usize) -> usize {
    match v.parse::<usize>() {
        Ok(v) if v <= max => v,
        Ok(v) => {
            eprintln!("count {} exceeded max {}", v, max);
            std::process::exit(7);
        }
        Err(_) => {
            eprintln!("failed to parse '{}' as uint", v);
            std::process::exit(7);
        }
    }
}
fn parse_share(v: &str) -> f64 {
    match v.parse::<f64>() {
        Ok(v) if v > 0.0 => v,
        Ok(v) => {
            eprintln!("share {} was outside valid range (0, inf)", v);
            std::process::exit(7);
        }
        Err(_) => {
            eprintln!("failed to parse '{}' as float", v);
            std::process::exit(7);
        }
    }
}

fn tess_helper<T: Tessellation>(mut tess: T, mode: &str, goal: &str) {
    let res = match mode {
        "dom:king" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::ClosedKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "odom:king" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::OpenKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "edom:king" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::ClosedKing>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "eodom:king" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::OpenKing>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "ld:king" => tess.try_satisfy::<codesets::LD<(isize, isize)>, adj::OpenKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "ic:king" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redic:king" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detic:king" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "erric:king" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "old:king" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redold:king" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detold:king" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenKing>(Goal::MeetOrBeat(parse_thresh(goal))),
        "errold:king" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenKing>(Goal::MeetOrBeat(parse_thresh(goal))),

        "dom:tri" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::ClosedTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "odom:tri" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::OpenTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "edom:tri" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::ClosedTri>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "eodom:tri" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::OpenTri>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "ld:tri" => tess.try_satisfy::<codesets::LD<(isize, isize)>, adj::OpenTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "ic:tri" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redic:tri" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detic:tri" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "erric:tri" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "old:tri" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redold:tri" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detold:tri" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenTri>(Goal::MeetOrBeat(parse_thresh(goal))),
        "errold:tri" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenTri>(Goal::MeetOrBeat(parse_thresh(goal))),

        "dom:grid" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::ClosedGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "odom:grid" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::OpenGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "edom:grid" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::ClosedGrid>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "eodom:grid" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::OpenGrid>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "ld:grid" => tess.try_satisfy::<codesets::LD<(isize, isize)>, adj::OpenGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "ic:grid" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redic:grid" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detic:grid" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "erric:grid" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "old:grid" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redold:grid" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detold:grid" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenGrid>(Goal::MeetOrBeat(parse_thresh(goal))),
        "errold:grid" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenGrid>(Goal::MeetOrBeat(parse_thresh(goal))),

        "dom:hex" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::ClosedHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "odom:hex" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::OpenHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "edom:hex" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::ClosedHex>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "eodom:hex" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::OpenHex>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "ld:hex" => tess.try_satisfy::<codesets::LD<(isize, isize)>, adj::OpenHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "ic:hex" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redic:hex" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detic:hex" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "erric:hex" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "old:hex" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redold:hex" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detold:hex" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenHex>(Goal::MeetOrBeat(parse_thresh(goal))),
        "errold:hex" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenHex>(Goal::MeetOrBeat(parse_thresh(goal))),

        "dom:tmb" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::ClosedTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "odom:tmb" => tess.try_satisfy::<codesets::DOM<(isize, isize)>, adj::OpenTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "edom:tmb" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::ClosedTMB>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "eodom:tmb" => tess.try_satisfy::<codesets::EDOM<(isize, isize)>, adj::OpenTMB>(Goal::Exactly(parse_exact(goal, tess.size()))),
        "ld:tmb" => tess.try_satisfy::<codesets::LD<(isize, isize)>, adj::OpenTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "ic:tmb" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redic:tmb" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detic:tmb" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "erric:tmb" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "old:tmb" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "redold:tmb" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "detold:tmb" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenTMB>(Goal::MeetOrBeat(parse_thresh(goal))),
        "errold:tmb" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenTMB>(Goal::MeetOrBeat(parse_thresh(goal))),

        _ => {
            eprintln!("unknown type: {}", mode);
            std::process::exit(4);
        }
    };
    match res {
        Some(min) => {
            let n = tess.size();
            let d = util::gcd(min, n);
            println!("found a {}/{} ({}) solution:\n{}", (min / d), (n / d), (min as f64 / n as f64), tess);
        },
        None => println!("no solution found"),
    }
}
fn theo_helper(set: &str, graph: &str, thresh: &str, strategy: TheoStrategy) {
    let thresh = parse_share(thresh);
    println!("lower bound for {} set on {} graph - {:?} thresh {}", set, graph, strategy, thresh);

    macro_rules! calc {
        ($set:ident, $adj:ident) => {
            LowerBoundSearcher::<codesets::$set<(isize, isize)>>::new().calc::<adj::$adj>(strategy, thresh, Some(&mut io::stdout()))
        }
    }
    macro_rules! family {
        ($open:ident, $closed:ident) => {
            match set {
                "dom" => calc!(DOM, $closed),
                "odom" => calc!(DOM, $open),
                "ic" => calc!(OLD, $closed),
                "red:ic" => calc!(RED, $closed),
                "det:ic" => calc!(DET, $closed),
                "err:ic" => calc!(ERR, $closed),
                "old" => calc!(OLD, $open),
                "red:old" => calc!(RED, $open),
                "det:old" => calc!(DET, $open),
                "err:old" => calc!(ERR, $open),
                _ => {
                    eprintln!("unknown set: {}", set);
                    std::process::exit(4);
                }
            }
        }
    }

    let ((n, k), f) = match graph {
        "king" => family!(OpenKing, ClosedKing),
        "tri" => family!(OpenTri, ClosedTri),
        "grid" => family!(OpenGrid, ClosedGrid),
        "hex" => family!(OpenHex, ClosedHex),
        "tmb" => family!(OpenTMB, ClosedTMB),
        _ => {
            eprintln!("unknown graph: {}", graph);
            std::process::exit(4);
        }
    };
    println!("found theo lower bound {}/{} ({})", n, k, f);
}
fn finite_helper(mut g: FiniteGraph, mode: &str, count: usize) {
    let success = match mode {
        "odom" => g.solver::<codesets::DOM<usize>>().find_solution(count),
        "old" => g.solver::<codesets::OLD<usize>>().find_solution(count),
        "red" => g.solver::<codesets::RED<usize>>().find_solution(count),
        "det" => g.solver::<codesets::DET<usize>>().find_solution(count),
        "err" => g.solver::<codesets::ERR<usize>>().find_solution(count),

        _ => {
            eprintln!("unknown type: {}", mode);
            std::process::exit(4);
        }
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

    let show_usage = |ret| -> ! {
        eprintln!("usage: {} (rect w h|geo shape) (old|det):(king|tri) [thresh]", args[0]);
        std::process::exit(ret);
    };

    if args.len() < 2 { show_usage(1); }
    match args[1].as_str() {
        "finite" => {
            if args.len() < 5 { show_usage(1); }
            let g = match FiniteGraph::with_shape(&args[2]) {
                Ok(g) => g,
                Err(e) => {
                    match e {
                        GraphLoadError::FileOpenFailure => eprintln!("failed to open graph file {}", args[2]),
                        GraphLoadError::InvalidFormat(msg) => eprintln!("file {} was invalid format: {}", args[2], msg),
                    }
                    std::process::exit(5);
                }
            };
            let count = match args[4].parse::<usize>() {
                Ok(n) => {
                    if n == 0 {
                        eprintln!("count cannot be zero");
                        std::process::exit(6);
                    }
                    if n > g.verts.len() {
                        eprintln!("count cannot be larger than graph size");
                        std::process::exit(6);
                    }
                    n
                }
                Err(_) => {
                    eprintln!("failed to parse '{}' as positive integer", args[4]);
                    std::process::exit(7);
                }
            };
            finite_helper(g, &args[3], count);
        }
        "theo" => {
            if args.len() < 5 { show_usage(1); }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::NoAveraging);
        }
        "theo-avg" => {
            if args.len() < 5 { show_usage(1); }
            theo_helper(&args[2], &args[3], &args[4], TheoStrategy::AverageWithNeighbors);
        }
        "rect" => {
            if args.len() < 6 { show_usage(1); }
            let rows: usize = args[2].parse().unwrap();
            let cols: usize = args[3].parse().unwrap();
            if rows < 2 || cols < 2 {
                eprintln!("1x1, 1xn, nx1 are not supported to avoid branch conditions\nthey also cannot result in lower than 2/3");
                std::process::exit(3);
            }
            let tess = RectTessellation::new(rows, cols);
            tess_helper(tess, &args[4], &args[5]);
        }
        "geo" => {
            let tess = match GeometryTessellation::with_shape(&args[2]) {
                Ok(x) => x,
                Err(e) => {
                    match e {
                        GeometryLoadResult::FileOpenFailure => eprintln!("failed to open tessellation file {}", args[2]),
                        GeometryLoadResult::InvalidFormat(msg) => eprintln!("file {} was invalid format: {}", args[2], msg),
                        GeometryLoadResult::TessellationFailure(msg) => eprintln!("file {} had a tessellation failure: {}", args[2], msg),
                    };
                    std::process::exit(5);
                },
            };
            println!("loaded geometry:\n{}", tess);
            tess_helper(tess, &args[3], &args[4])
        }
        _ => show_usage(1),
    };
}

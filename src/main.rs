use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::io::{BufRead, BufReader};
use std::fs::File;
use std::path::Path;

mod util;
mod adj;
mod codesets;

use adj::AdjacentIterator;

trait Solver {
    fn get_locating_code<Adj>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> where Adj: adj::AdjacentIterator;
    fn is_old<Adj>(&mut self) -> bool where Adj: adj::AdjacentIterator;
    fn try_satisfy<Adj>(&mut self) -> Option<usize> where Adj: adj::AdjacentIterator;
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
                let code = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.add(code) {
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
                let code = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.can_add(&code) || !self.codes.add(code) {
                    return false;
                }
            }
        }
        for r in 1 ..= self.src.rows as isize - 2 {
            for &c in &[-1, 0, self.src.cols as isize - 1, self.src.cols as isize] {
                let code = self.get_locating_code::<Adj>((r, c));
                if !self.interior_codes.can_add(&code) || !self.codes.add(code) {
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
        } else if pos < self.base.src.old_set.len() {
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
    fn try_satisfy<Adj: adj::AdjacentIterator>(&mut self) -> Option<usize> {
        for x in &mut self.base.src.old_set { *x = false; }
        self.base.prevs.clear();
        if self.calc_old_min_interior::<Adj>(0) { Some(self.base.needed) } else { None }
    }
}

trait Tessellation: fmt::Display {
    fn size(&self) -> usize;
    fn try_satisfy<Codes, Adj>(&mut self, thresh: f64) -> Option<usize>
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
        assert!(rows >= 2);
        assert!(cols >= 2);

        RectTessellation {
            rows, cols,
            old_set: vec![false; rows * cols],
            phase: (0, 0),
        }
    }
    fn solver<Codes>(&mut self, thresh: f64) -> RectSolver<'_, Codes>
    where Codes: codesets::Set<(isize, isize)>
    {
        let needed = (self.old_set.len() as f64 * thresh).floor() as usize;
        let (r, c) = (self.rows, self.cols);
        RectSolver::<Codes> {
            base: RectSolverBase::<Codes> {
                src: self,
                codes: Default::default(),
                interior_codes: Default::default(),
                needed,
                prevs: Vec::with_capacity(needed),
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
    fn try_satisfy<Codes, Adj>(&mut self, thresh: f64) -> Option<usize>
    where Codes: codesets::Set<(isize, isize)>, Adj: adj::AdjacentIterator
    {
        self.solver::<Codes>(thresh).try_satisfy::<Adj>()
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
            let code = self.get_locating_code::<Adj>(*p);
            if !self.codes.add(code) {
                return false;
            }
        }
        true
    }
    fn calc_old_min_interior<'b, Adj, P>(&mut self, mut pos: P) -> bool
    where Adj: adj::AdjacentIterator, P: Iterator<Item = &'b (isize, isize)> + Clone
    {
        if self.needed == self.old_set.len() {
            if self.is_old::<Adj>() {
                return true;
            }
        } else if let Some(&p) = pos.next() {
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
            let mapped = self.tessellation_map.get(&x).unwrap();
            if self.old_set.contains(mapped) {
                v.push(x);
            }
        }
        v
    }
    fn is_old<Adj: adj::AdjacentIterator>(&mut self) -> bool {
        self.codes.clear();
        for pos in self.shape_with_padding {
            let code = self.get_locating_code::<Adj>(*pos);
            if !self.codes.add(code) {
                return false;
            }
        }
        true
    }
    fn try_satisfy<Adj: adj::AdjacentIterator>(&mut self) -> Option<usize> {
        self.old_set.clear();
        if self.calc_old_min_interior::<Adj, _>(self.shape.iter()) { Some(self.needed) } else { None }
    }
}

struct GeometryTessellation {
    shape: BTreeSet<(isize, isize)>,
    interior: BTreeSet<(isize, isize)>,
    shape_with_padding: BTreeSet<(isize, isize)>,
    tessellation_map: HashMap<(isize, isize), (isize, isize)>,
    first_per_row: HashSet<(isize, isize)>,
    old_set: BTreeSet<(isize, isize)>,
    basis_a: (isize, isize),
    basis_b: (isize, isize),
}
impl fmt::Display for GeometryTessellation {
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
            write!(f, "{} ", if self.old_set.contains(x) { 1 } else { 0 })?;
        }
        writeln!(f)?;
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

        let shape = {
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
            shape
        };
        let interior = {
            let boundary: BTreeSet<_> = shape.iter().filter(|x| adj::OpenKing::new(x.0, x.1).any(|y| !shape.contains(&y))).cloned().collect();
            &shape - &boundary
        };
        let first_per_row = {
            let mut s: HashSet<(isize, isize)> = Default::default();
            let mut r = !0;
            for p in &shape {
                if p.0 != r {
                    r = p.0;
                    s.insert(*p);
                }
            }
            s
        };

        let shape_with_padding: BTreeSet<_> = {
            let mut t = shape.clone();
            t.extend(shape.iter().flat_map(|x| adj::OpenKing::new(x.0, x.1)));
            t
        };
        let shape_with_extra_padding: BTreeSet<_> = {
            let mut t = shape_with_padding.clone();
            t.extend(shape_with_padding.iter().flat_map(|x| adj::OpenKing::new(x.0, x.1)));
            t
        };

        let tessellation_map = {
            let mut p: HashSet<(isize, isize)> = HashSet::with_capacity(shape.len() * 25);
            let mut m: HashMap<(isize, isize), (isize, isize)> = HashMap::with_capacity(shape.len() * 9);

            for &to in &shape {
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
            shape, interior, shape_with_padding, tessellation_map, first_per_row,
            basis_a, basis_b,
            old_set: Default::default(),
        })
    }
    fn solver<Codes>(&mut self, thresh: f64) -> GeometrySolver<'_, Codes>
    where Codes: codesets::Set<(isize, isize)>
    {
        assert!(thresh > 0.0 && thresh <= 1.0);
        self.old_set.clear();

        let needed = (self.size() as f64 * thresh).floor() as usize;
        GeometrySolver::<Codes> {
            shape: &self.shape,
            interior: &self.interior,
            shape_with_padding: &self.shape_with_padding,
            tessellation_map: &self.tessellation_map,
            first_per_row: &self.first_per_row,
            old_set: &mut self.old_set,

            codes: Default::default(),
            needed,
        }
    }
}
impl Tessellation for GeometryTessellation {
    fn size(&self) -> usize {
        self.shape.len()
    }
    fn try_satisfy<Codes, Adj>(&mut self, thresh: f64) -> Option<usize>
    where Codes: codesets::Set<(isize, isize)>, Adj: adj::AdjacentIterator
    {
        self.solver::<Codes>(thresh).try_satisfy::<Adj>()
    }
}

type OverThreshHandler = dyn FnMut(&[bool], f64);
struct LowerBoundSearcher<'a, Codes> {
    data: [bool; 25],
    iter_pos: Vec<usize>,
    codes: Codes,
    highest: f64,
    thresh: f64,
    over_thresh_handler: Option<&'a mut OverThreshHandler>,
}
impl<'a, Codes> LowerBoundSearcher<'a, Codes>
where Codes: codesets::Set<(isize, isize)>
{
    fn to_index(&self, row: isize, col: isize) -> usize {
        row as usize * 5 + col as usize
    }
    fn get_locating_code<Adj: adj::AdjacentIterator>(&self, row: isize, col: isize) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(9);
        for p in Adj::new(row, col) {
            if self.data[self.to_index(p.0, p.1)] {
                v.push(p);
            }
        }
        v
    }
    fn get_locating_code_size<Adj: adj::AdjacentIterator>(&self, row: isize, col: isize) -> usize {
        Adj::new(row, col).filter(|p| self.data[self.to_index(p.0, p.1)]).count()
    }
    fn is_valid<Adj: adj::AdjacentIterator>(&mut self) -> bool {
        self.codes.clear();
        for p in Adj::closed_neighborhood_unord(2, 2) {
            let code = self.get_locating_code::<Adj>(p.0, p.1);
            if !self.codes.add(code) {
                return false;
            }
        }
        true
    }
    fn calc_share<Adj: adj::AdjacentIterator>(&self, row: isize, col: isize) -> f64 {
        assert!(self.data[self.to_index(row, col)]);

        let mut share = 0.0;
        for p in Adj::new(row, col) {
            let c = self.get_locating_code_size::<Adj>(p.0, p.1);
            share += 1.0 / c as f64;
        }
        share
    }
    fn calc_recursive<Adj: adj::AdjacentIterator>(&mut self, pos: usize) {
        if pos >= self.iter_pos.len() {
            if self.is_valid::<Adj>() {
                let share = self.calc_share::<Adj>(2, 2);
                if share > self.thresh {
                    match self.over_thresh_handler {
                        Some(ref mut f) => f(&self.data, share),
                        None => (),
                    };
                }
                if self.highest < share {
                    self.highest = share;
                }
            }
        }
        else {
            // recurse on both possibilities
            self.data[self.iter_pos[pos]] = true;
            self.calc_recursive::<Adj>(pos + 1);
            self.data[self.iter_pos[pos]] = false;
            self.calc_recursive::<Adj>(pos + 1);
        }
    }
    fn calc<Adj: adj::AdjacentIterator>(&mut self, thresh: f64, over_thresh_handler: Option<&'a mut OverThreshHandler>) -> ((usize, usize), f64) {
        {
            // generate the iteration area - center extended twice, excluding center itself
            let area: BTreeSet<_> = Adj::new(2, 2).collect();
            let mut t = area.clone();
            t.extend(area.into_iter().flat_map(|p| Adj::new(p.0, p.1)));
            t.remove(&(2, 2)); // remove center in case it was added from the extension

            self.iter_pos.clear();
            for p in t.into_iter() {
                self.iter_pos.push(self.to_index(p.0, p.1));
            }
        }
        
        // everything starts as false except the center vertex
        for x in self.data.iter_mut() { *x = false; }
        self.data[self.to_index(2, 2)] = true;

        // set current highest as zero and begin recursive search
        self.highest = 0.0;
        self.thresh = thresh;
        self.over_thresh_handler = over_thresh_handler;
        self.calc_recursive::<Adj>(0);

        // lcm(1..=9) = 2520, so multiply and divide by 2520 to create an exact fractional representation
        let v = (self.highest * 2520.0).round() as usize;
        let d = util::gcd(v, 2520);
        ((2520 / d, v / d), 1.0 / self.highest)
    }
    fn new() -> Self {
        Self {
            data: [false; 25],
            iter_pos: vec![],
            codes: Default::default(),
            highest: 0.0,
            thresh: 0.0,
            over_thresh_handler: None,
        }
    }
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
            let code = self.get_locating_code(i);
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
    let mut gg = ggg.solver::<codesets::OLD<(isize, isize)>>(0.9);
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

#[test]
fn test_lower_bound_index() {
    let v = LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new();
    assert_eq!(v.to_index(0, 0), 0);
    assert_eq!(v.to_index(2, 1), 11);
}

fn tess_helper<T: Tessellation>(mut tess: T, mode: &str, thresh: f64) {
    let res = match mode {
        "ic:king" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedKing>(thresh),
        "redic:king" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedKing>(thresh),
        "detic:king" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedKing>(thresh),
        "erric:king" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedKing>(thresh),
        "old:king" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenKing>(thresh),
        "red:king" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenKing>(thresh),
        "det:king" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenKing>(thresh),
        "err:king" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenKing>(thresh),

        "ic:tri" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedTri>(thresh),
        "redic:tri" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedTri>(thresh),
        "detic:tri" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedTri>(thresh),
        "erric:tri" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedTri>(thresh),
        "old:tri" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenTri>(thresh),
        "red:tri" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenTri>(thresh),
        "det:tri" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenTri>(thresh),
        "err:tri" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenTri>(thresh),

        "ic:grid" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedGrid>(thresh),
        "redic:grid" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedGrid>(thresh),
        "detic:grid" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedGrid>(thresh),
        "erric:grid" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedGrid>(thresh),
        "old:grid" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenGrid>(thresh),
        "red:grid" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenGrid>(thresh),
        "det:grid" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenGrid>(thresh),
        "err:grid" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenGrid>(thresh),

        "ic:hex" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedHex>(thresh),
        "redic:hex" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedHex>(thresh),
        "detic:hex" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedHex>(thresh),
        "erric:hex" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedHex>(thresh),
        "old:hex" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenHex>(thresh),
        "red:hex" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenHex>(thresh),
        "det:hex" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenHex>(thresh),
        "err:hex" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenHex>(thresh),

        "ic:tmb" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::ClosedTMB>(thresh),
        "redic:tmb" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::ClosedTMB>(thresh),
        "detic:tmb" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::ClosedTMB>(thresh),
        "erric:tmb" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::ClosedTMB>(thresh),
        "old:tmb" => tess.try_satisfy::<codesets::OLD<(isize, isize)>, adj::OpenTMB>(thresh),
        "red:tmb" => tess.try_satisfy::<codesets::RED<(isize, isize)>, adj::OpenTMB>(thresh),
        "det:tmb" => tess.try_satisfy::<codesets::DET<(isize, isize)>, adj::OpenTMB>(thresh),
        "err:tmb" => tess.try_satisfy::<codesets::ERR<(isize, isize)>, adj::OpenTMB>(thresh),

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
        None => println!("no solution found within thresh {}", thresh),
    }
}
fn theo_helper(mode: &str, thresh: f64) {
    let mut handler = move |data: &[bool], share: f64| {
        println!("problem: {}", share);
        for v in data.chunks(5) {
            for &x in v {
                print!("{} ", if x { 1 } else { 0 });
            }
            println!();
        }
        println!();
    };
    let ((n, k), f) = match mode {
        "ic:king" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::ClosedKing>(thresh, Some(&mut handler)),
        "old:king" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenKing>(thresh, Some(&mut handler)),
        "red:king" => LowerBoundSearcher::<codesets::RED<(isize, isize)>>::new().calc::<adj::OpenKing>(thresh, Some(&mut handler)),
        "det:king" => LowerBoundSearcher::<codesets::DET<(isize, isize)>>::new().calc::<adj::OpenKing>(thresh, Some(&mut handler)),
        "err:king" => LowerBoundSearcher::<codesets::ERR<(isize, isize)>>::new().calc::<adj::OpenKing>(thresh, Some(&mut handler)),

        "ic:tri" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::ClosedTri>(thresh, Some(&mut handler)),
        "old:tri" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenTri>(thresh, Some(&mut handler)),
        "red:tri" => LowerBoundSearcher::<codesets::RED<(isize, isize)>>::new().calc::<adj::OpenTri>(thresh, Some(&mut handler)),
        "det:tri" => LowerBoundSearcher::<codesets::DET<(isize, isize)>>::new().calc::<adj::OpenTri>(thresh, Some(&mut handler)),
        "err:tri" => LowerBoundSearcher::<codesets::ERR<(isize, isize)>>::new().calc::<adj::OpenTri>(thresh, Some(&mut handler)),

        "ic:grid" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::ClosedGrid>(thresh, Some(&mut handler)),
        "old:grid" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenGrid>(thresh, Some(&mut handler)),
        "red:grid" => LowerBoundSearcher::<codesets::RED<(isize, isize)>>::new().calc::<adj::OpenGrid>(thresh, Some(&mut handler)),
        "det:grid" => LowerBoundSearcher::<codesets::DET<(isize, isize)>>::new().calc::<adj::OpenGrid>(thresh, Some(&mut handler)),
        "err:grid" => LowerBoundSearcher::<codesets::ERR<(isize, isize)>>::new().calc::<adj::OpenGrid>(thresh, Some(&mut handler)),

        "ic:hex" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::ClosedHex>(thresh, Some(&mut handler)),
        "old:hex" => LowerBoundSearcher::<codesets::OLD<(isize, isize)>>::new().calc::<adj::OpenHex>(thresh, Some(&mut handler)),
        "red:hex" => LowerBoundSearcher::<codesets::RED<(isize, isize)>>::new().calc::<adj::OpenHex>(thresh, Some(&mut handler)),
        "det:hex" => LowerBoundSearcher::<codesets::DET<(isize, isize)>>::new().calc::<adj::OpenHex>(thresh, Some(&mut handler)),
        "err:hex" => LowerBoundSearcher::<codesets::ERR<(isize, isize)>>::new().calc::<adj::OpenHex>(thresh, Some(&mut handler)),

        _ => {
            eprintln!("unknown type: {}", mode);
            std::process::exit(4);
        }
    };

    println!("found theo lower bound {}/{} ({})", n, k, f);
}
fn finite_helper(mut g: FiniteGraph, mode: &str, count: usize) {
    let success = match mode {
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

    let parse_thresh = |a: &str| {
        match a.parse::<f64>() {
            Ok(v) if v > 0.0 && v <= 1.0 => v,
            Ok(_) => {
                eprintln!("thresh must be (0, 1]");
                std::process::exit(6);
            }
            Err(_) => {
                eprintln!("failed to parse thresh as a floating point value");
                std::process::exit(7);
            }
        }
    };
    let parse_share = |a: &str| {
        match a.parse::<f64>() {
            Ok(v) if v >= 1.0 => v,
            Ok(_) => {
                eprintln!("share must be [1, inf)");
                std::process::exit(6);
            }
            Err(_) => {
                eprintln!("failed to parse share as a floating point value");
                std::process::exit(7);
            }
        }
    };
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
            if args.len() < 4 { show_usage(1); }
            let thresh = parse_share(&args[3]);
            theo_helper(&args[2], thresh);
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
            let thresh = parse_thresh(&args[5]);
            tess_helper(tess, &args[4], thresh)
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
            let thresh = parse_thresh(&args[4]);
            println!("loaded geometry:\n{}", tess);
            tess_helper(tess, &args[3], thresh)
        }
        _ => show_usage(1),
    };
}

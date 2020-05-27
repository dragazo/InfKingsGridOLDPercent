use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::io::{BufRead, BufReader};
use std::fs::File;
use std::path::Path;
//use rand::Rng;

// additionally required to iterate in lexicographic sorted order and not have duplicates (see unit tests below)
trait AdjacentIterator: Iterator<Item = (isize, isize)> {
    fn new(row: isize, col: isize) -> Self;
}

struct Adjacent8 {
    row: isize,
    col: isize,
    state: usize,
}
impl AdjacentIterator for Adjacent8 {
    fn new(row: isize, col: isize) -> Self {
        Self { row, col, state: 0 }
    }
}
impl Iterator for Adjacent8 {
    type Item = (isize, isize);
    fn next(&mut self) -> Option<Self::Item> {
        let r = self.row;
        let c = self.col;

        let v = match self.state {
            0 => (r - 1, c - 1),
            1 => (r - 1, c),
            2 => (r - 1, c + 1),

            3 => (r, c - 1),
            4 => (r, c + 1),

            5 => (r + 1, c - 1),
            6 => (r + 1, c),
            7 => (r + 1, c + 1),

            _ => return None,
        };
        self.state += 1;
        Some(v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let v = 8 - self.state;
        (v, Some(v))
    }
}
impl ExactSizeIterator for Adjacent8 {}

struct Adjacent4 {
    row: isize,
    col: isize,
    state: usize,
}
impl AdjacentIterator for Adjacent4 {
    fn new(row: isize, col: isize) -> Self {
        Self { row, col, state: 0 }
    }
}
impl Iterator for Adjacent4 {
    type Item = (isize, isize);
    fn next(&mut self) -> Option<Self::Item> {
        let r = self.row;
        let c = self.col;

        let v = match self.state {
            0 => (r - 1, c),
            1 => (r, c - 1),
            2 => (r, c + 1),
            3 => (r + 1, c),
            _ => return None,
        };
        self.state += 1;
        Some(v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let v = 4 - self.state;
        (v, Some(v))
    }
}
impl ExactSizeIterator for Adjacent4 {}

struct AdjacentTriangle {
    row: isize,
    col: isize,
    state: usize,
}
impl AdjacentIterator for AdjacentTriangle {
    fn new(row: isize, col: isize) -> Self {
        Self { row, col, state: 0 }
    }
}
impl Iterator for AdjacentTriangle {
    type Item = (isize, isize);
    fn next(&mut self) -> Option<Self::Item> {
        let r = self.row;
        let c = self.col;

        let v = match self.state {
            0 => (r - 1, c - 1),
            1 => (r - 1, c),

            2 => (r, c - 1),
            3 => (r, c + 1),

            4 => (r + 1, c),
            5 => (r + 1, c + 1),

            _ => return None,
        };
        self.state += 1;
        Some(v)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let v = 6 - self.state;
        (v, Some(v))
    }
}
impl ExactSizeIterator for AdjacentTriangle {}

trait CodeSet: Default {
    fn clear(&mut self);
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn can_add(&self, code: &Vec<(isize, isize)>) -> bool;
    fn add(&mut self, code: Vec<(isize, isize)>) -> bool;
}

#[derive(Default)]
struct OLDSet {
    codes: BTreeSet<Vec<(isize, isize)>>,
}
impl CodeSet for OLDSet {
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn is_empty(&self) -> bool {
        self.codes.is_empty()
    }
    fn len(&self) -> usize {
        self.codes.len()
    }
    fn can_add(&self, code: &Vec<(isize, isize)>) -> bool {
        !code.is_empty() && !self.codes.contains(code)
    }
    fn add(&mut self, code: Vec<(isize, isize)>) -> bool {
        if self.can_add(&code) {
            self.codes.insert(code);
            true
        }
        else { false }
    }
}

#[derive(Default)]
struct DETSet {
    codes: Vec<Vec<(isize, isize)>>,
}
impl CodeSet for DETSet {
    fn clear(&mut self) {
        self.codes.clear();
    }
    fn is_empty(&self) -> bool {
        self.codes.is_empty()
    }
    fn len(&self) -> usize {
        self.codes.len()
    }
    fn can_add(&self, code: &Vec<(isize, isize)>) -> bool {
        if code.len() < 2 { return false; }
        for other in &self.codes {
            let equal = count_equal(&*other, code);
            if equal + 2 > other.len() && equal + 2 > code.len() {
                return false;
            }
        }
        true
    }
    fn add(&mut self, code: Vec<(isize, isize)>) -> bool {
        if self.can_add(&code) {
            self.codes.push(code);
            true
        }
        else { false }
    }
}

trait Solver {
    fn get_locating_code<Adj>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> where Adj: AdjacentIterator;
    fn is_old<Adj>(&mut self) -> bool where Adj: AdjacentIterator;
    fn try_satisfy<Adj>(&mut self) -> Option<usize> where Adj: AdjacentIterator;
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
impl<Codes> RectSolverBase<'_, Codes> where Codes: CodeSet {
    fn id_to_inside(&self, row: isize, col: isize) -> usize {
        let col_fix = if row < 0 { col - self.src.phase.0 } else if row >= self.src.rows as isize { col + self.src.phase.0 } else { col };
        let row_fix = if col < 0 { row - self.src.phase.1 } else if col >= self.src.cols as isize { row + self.src.phase.1 } else { row };

        let r = (row_fix + 2 * self.src.rows as isize) as usize % self.src.rows;
        let c = (col_fix + 2 * self.src.cols as isize) as usize % self.src.cols;
        r * self.src.cols + c
    }
    fn get_locating_code<Adj: AdjacentIterator>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(8);
        for x in Adj::new(pos.0, pos.1) {
            if self.src.old_set[self.id_to_inside(x.0, x.1)] {
                v.push(x)
            }
        }
        v
    }
    fn is_old_interior_up_to<Adj: AdjacentIterator>(&mut self, row: isize) -> bool {
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
    fn is_old_with_current_phase<Adj: AdjacentIterator>(&mut self) -> bool {
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
where Codes: CodeSet
{
    fn calc_old_min_interior<Adj: AdjacentIterator>(&mut self, pos: usize) -> bool {
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
where Codes: CodeSet
{
    fn get_locating_code<Adj: AdjacentIterator>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        self.base.get_locating_code::<Adj>(pos)
    }
    fn is_old<Adj: AdjacentIterator>(&mut self) -> bool {
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
    fn try_satisfy<Adj: AdjacentIterator>(&mut self) -> Option<usize> {
        for x in &mut self.base.src.old_set { *x = false; }
        self.base.prevs.clear();
        if self.calc_old_min_interior::<Adj>(0) { Some(self.base.needed) } else { None }
    }
}

trait Tessellation: fmt::Display {
    fn size(&self) -> usize;
    fn try_satisfy<Codes, Adj>(&mut self, thresh: f64) -> Option<usize> where Codes: CodeSet, Adj: AdjacentIterator;
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
    fn solver<Codes: CodeSet>(&mut self, thresh: f64) -> RectSolver<'_, Codes> {
        let needed = (self.old_set.len() as f64 * thresh).ceil() as usize - 1;
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
    where Codes: CodeSet, Adj: AdjacentIterator
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
    prevs: Vec<(isize, isize)>,
}
impl<'a, Codes> GeometrySolver<'a, Codes>
where Codes: CodeSet
{
    fn is_old_interior_up_to<Adj: AdjacentIterator>(&mut self, row: isize) -> bool {
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
    where Adj: AdjacentIterator, P: Iterator<Item = &'b (isize, isize)> + Clone
    {
        if self.needed == self.prevs.len() {
            if self.is_old::<Adj>() {
                return true;
            }
        } else if let Some(&p) = pos.next() {
            let good_so_far = !self.first_per_row.contains(&p) || self.is_old_interior_up_to::<Adj>(p.0);

            if good_so_far {
                self.old_set.insert(p);
                self.prevs.push(p);
                if self.calc_old_min_interior::<Adj, _>(pos.clone()) {
                    return true;
                }
                self.prevs.pop();
                self.old_set.remove(&p);

                return self.calc_old_min_interior::<Adj, _>(pos);
            }
        }

        false
    }
}
impl<Codes> Solver for GeometrySolver<'_, Codes>
where Codes: CodeSet
{
    fn get_locating_code<Adj: AdjacentIterator>(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(8);
        for x in Adj::new(pos.0, pos.1) {
            let mapped = self.tessellation_map.get(&x).unwrap();
            if self.old_set.contains(mapped) {
                v.push(x);
            }
        }
        v
    }
    fn is_old<Adj: AdjacentIterator>(&mut self) -> bool {
        self.codes.clear();
        for pos in self.shape_with_padding {
            let code = self.get_locating_code::<Adj>(*pos);
            if !self.codes.add(code) {
                return false;
            }
        }
        true
    }
    fn try_satisfy<Adj: AdjacentIterator>(&mut self) -> Option<usize> {
        self.old_set.clear();
        self.prevs.clear();
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
            let boundary: BTreeSet<_> = shape.iter().filter(|x| Adjacent8::new(x.0, x.1).any(|y| !shape.contains(&y))).cloned().collect();
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
            shape.clone().into_iter().flat_map(|x| Adjacent8::new(x.0, x.1)).collect()
        };
        let shape_with_extra_padding: BTreeSet<_> = {
            shape_with_padding.clone().into_iter().flat_map(|x| Adjacent8::new(x.0, x.1)).collect()
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
    where Codes: CodeSet
    {
        assert!(thresh > 0.0 && thresh <= 1.0);
        self.old_set.clear();

        let needed = (self.size() as f64 * thresh).ceil() as usize - 1;
        GeometrySolver::<Codes> {
            shape: &self.shape,
            interior: &self.interior,
            shape_with_padding: &self.shape_with_padding,
            tessellation_map: &self.tessellation_map,
            first_per_row: &self.first_per_row,
            old_set: &mut self.old_set,

            codes: Default::default(),
            needed,
            prevs: Vec::with_capacity(needed),
        }
    }
}
impl Tessellation for GeometryTessellation {
    fn size(&self) -> usize {
        self.shape.len()
    }
    fn try_satisfy<Codes, Adj>(&mut self, thresh: f64) -> Option<usize>
    where Codes: CodeSet, Adj: AdjacentIterator
    {
        self.solver::<Codes>(thresh).try_satisfy::<Adj>()
    }
}

struct LowerBoundSearcher<Codes> {
    data: [bool; 25],
    iter_pos: Vec<usize>,
    codes: Codes,
    highest: f64,
    thresh: f64,
}
impl<Codes: CodeSet> LowerBoundSearcher<Codes> {
    fn to_index(&self, row: isize, col: isize) -> usize {
        row as usize * 5 + col as usize
    }
    fn get_locating_code<Adj: AdjacentIterator>(&self, row: isize, col: isize) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(8);
        for p in Adj::new(row, col) {
            if self.data[self.to_index(p.0, p.1)] {
                v.push(p);
            }
        }
        v
    }
    fn get_locating_code_size<Adj: AdjacentIterator>(&self, row: isize, col: isize) -> usize {
        Adj::new(row, col).filter(|p| self.data[self.to_index(p.0, p.1)]).count()
    }
    fn is_valid<Adj: AdjacentIterator>(&mut self) -> bool {
        self.codes.clear();
        for p in std::iter::once((2, 2)).chain(Adj::new(2, 2)) {
            let code = self.get_locating_code::<Adj>(p.0, p.1);
            if !self.codes.add(code) {
                return false;
            }
        }
        true
    }
    fn calc_share<Adj: AdjacentIterator>(&self, row: isize, col: isize) -> f64 {
        assert!(self.data[self.to_index(row, col)]);

        let mut share = 0.0;
        for p in Adj::new(row, col) {
            let c = self.get_locating_code_size::<Adj>(p.0, p.1);
            share += 1.0 / c as f64;
        }
        share
    }
    fn calc_recursive<Adj: AdjacentIterator>(&mut self, pos: usize) {
        if pos >= self.iter_pos.len() {
            if self.is_valid::<Adj>() {
                let share = self.calc_share::<Adj>(2, 2);
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
    fn calc<Adj: AdjacentIterator>(&mut self, thresh: f64) -> ((usize, usize), f64) {
        {
            // generate the iteration area - center extended twice, excluding center itself
            let mut area: BTreeSet<(isize, isize)> = Default::default();
            for p in Adj::new(2, 2) {
                area.insert(p);
            }
            let mut t = area.into_iter().flat_map(|p| Adj::new(p.0, p.1)).collect::<BTreeSet<_>>();
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
        self.calc_recursive::<Adj>(0);

        // lcm(1..=8) = 840, so multiply and divide by 840 to create an exact fractional representation
        let v = (self.highest * 840.0).round() as usize;
        let d = gcd(v, 840);
        ((840 / d, v / d), 1.0 / self.highest)
    }
    fn new() -> Self {
        Self {
            data: [false; 25],
            iter_pos: vec![],
            codes: Default::default(),
            highest: 0.0,
            thresh: 0.0,
        }
    }
}

fn count_equal<T>(arr_1: &[T], arr_2: &[T]) -> usize
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
// source: https://doc.rust-lang.org/std/ops/trait.Div.html
fn gcd(mut x: usize, mut y: usize) -> usize {
    while y != 0 {
        let t = y;
        y = x % y;
        x = t;
    }
    x
}

// Vec::is_sorted is nightly-only, so use this workaround
#[cfg(test)]
fn is_sorted<T: PartialOrd>(arr: &[T]) -> bool {
    for w in arr.windows(2) {
        if w[0] > w[1] {
            return false;
        }
    }
    true
}

#[test]
fn test_det_set() {
    let mut s: DETSet = Default::default();
    
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
#[test]
fn test_count_equal() {
    assert_eq!(count_equal(&[0i32;0], &[]), 0);
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
#[test]
fn test_rect_pos() {
    let mut ggg = RectTessellation::new(4, 4);
    let mut gg = ggg.solver::<OLDSet>(0.9);
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
fn test_adjacent4_sorted() {
    for &(r, c) in &[(0, 0), (4, 2), (-1, 2), (-18, -4), (1, -7)] {
        let v: Vec<_> = Adjacent4::new(r, c).collect();
        assert!(is_sorted(&v));
    }
}
#[test]
fn test_adjacent8_sorted() {
    for &(r, c) in &[(0, 0), (4, 2), (-1, 2), (-18, -4), (1, -7)] {
        let v: Vec<_> = Adjacent8::new(r, c).collect();
        assert!(is_sorted(&v));
    }
}
#[test]
fn test_adjacent_tri_sorted() {
    for &(r, c) in &[(0, 0), (4, 2), (-1, 2), (-18, -4), (1, -7)] {
        let v: Vec<_> = AdjacentTriangle::new(r, c).collect();
        assert!(is_sorted(&v));
    }
}
#[test]
fn test_lower_bound_index() {
    let v = LowerBoundSearcher::<OLDSet>::new();
    assert_eq!(v.to_index(0, 0), 0);
    assert_eq!(v.to_index(2, 1), 11);
}

fn tess_helper<T: Tessellation>(mut tess: T, mode: &str, thresh: f64) {
    let res = match mode {
        "old:king" => tess.try_satisfy::<OLDSet, Adjacent8>(thresh),
        "det:king" => tess.try_satisfy::<DETSet, Adjacent8>(thresh),

        "old:tri" => tess.try_satisfy::<OLDSet, AdjacentTriangle>(thresh),
        "det:tri" => tess.try_satisfy::<DETSet, AdjacentTriangle>(thresh),

        "old:grid" => tess.try_satisfy::<OLDSet, Adjacent4>(thresh),
        "det:grid" => tess.try_satisfy::<DETSet, Adjacent4>(thresh),

        _ => {
            eprintln!("unknown type: {}", mode);
            std::process::exit(4);
        }
    };
    match res {
        Some(min) => {
            let n = tess.size();
            let d = gcd(min, n);
            println!("found a {}/{} ({}) solution:\n{}", (min / d), (n / d), (min as f64 / n as f64), tess);
        },
        None => println!("no solution found under thresh {}", thresh),
    }
}
fn theo_helper(mode: &str, thresh: f64) {
    let ((n, k), f) = match mode {
        "old:king" => LowerBoundSearcher::<OLDSet>::new().calc::<Adjacent8>(thresh),
        "det:king" => LowerBoundSearcher::<DETSet>::new().calc::<Adjacent8>(thresh),

        "old:tri" => LowerBoundSearcher::<OLDSet>::new().calc::<AdjacentTriangle>(thresh),
        "det:tri" => LowerBoundSearcher::<DETSet>::new().calc::<AdjacentTriangle>(thresh),

        "old:grid" => LowerBoundSearcher::<OLDSet>::new().calc::<Adjacent4>(thresh),
        "det:grid" => LowerBoundSearcher::<DETSet>::new().calc::<Adjacent4>(thresh),

        _ => {
            eprintln!("unknown type: {}", mode);
            std::process::exit(4);
        }
    };

    println!("found theo lower bound {}/{} ({})", n, k, f);
}
fn main() {
    let args: Vec<String> = std::env::args().collect();

    let parse_thresh = |a: &str| {
        match a.parse::<f64>() {
            Ok(v) if v > 0.0 && v <= 1.0 => v,
            Ok(_) => {
                eprintln!("thresh must be (0, 1]");
                std::process::exit(6);
            },
            Err(_) => {
                eprintln!("failed to parse thresh as a floating point value");
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
        "theo" => {
            if args.len() < 4 { show_usage(1); }
            let thresh = parse_thresh(&args[3]);
            theo_helper(&args[2], thresh);
        }
        "rect" => {
            if args.len() < 6 { show_usage(1); }
            let (rows, cols) = {
                let rows: usize = args[2].parse().unwrap();
                let cols: usize = args[3].parse().unwrap();
                if rows >= cols { (rows, cols) } else { (cols, rows) }
            };
            if cols < 2 {
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

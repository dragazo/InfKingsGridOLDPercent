use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::io::{BufRead, BufReader};
use std::fs::File;
use std::path::Path;
//use rand::Rng;

// additionally required to iterate in lexicographic sorted order (see unit tests below)
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
    fn can_add(&self, code: &Vec<(isize, isize)>) -> bool {
        if code.len() < 2 { return false; }
        for other in &self.codes {
            if code.iter().filter(|x| !other.contains(x)).count() < 2 && other.iter().filter(|x| !code.contains(x)).count() < 2 {
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

struct RectSolver<'a, Codes> {
    src: &'a mut RectTessellation,
    phases: Vec<(isize, isize)>,
    codes: Codes,
    interior_codes: Codes,
    needed: usize,
    prevs: Vec<(isize, isize)>,
}
impl<Codes> RectSolver<'_, Codes> where Codes: CodeSet {
    fn id_to_inside(&self, row: isize, col: isize) -> usize {
        let col_fix = if row < 0 { col - self.src.phase.0 } else if row >= self.src.rows as isize { col + self.src.phase.0 } else { col };
        let row_fix = if col < 0 { row - self.src.phase.1 } else if col >= self.src.cols as isize { row + self.src.phase.1 } else { row };

        let r = (row_fix + 2 * self.src.rows as isize) as usize % self.src.rows;
        let c = (col_fix + 2 * self.src.cols as isize) as usize % self.src.cols;
        r * self.src.cols + c
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
    fn calc_old_min_interior<Adj: AdjacentIterator>(&mut self, pos: usize) -> bool {
        if self.needed == self.prevs.len() {
            if self.is_old::<Adj>() {
                return true;
            }
        } else if pos < self.src.old_set.len() {
            let p = ((pos / self.src.cols) as isize, (pos % self.src.cols) as isize);

            let good_so_far = p.1 != 0 || self.is_old_interior_up_to::<Adj>(p.0);

            if good_so_far {
                self.src.old_set[pos] = true;
                self.prevs.push(p);
                if self.calc_old_min_interior::<Adj>(pos + 1) {
                    return true;
                }
                self.prevs.pop();
                self.src.old_set[pos] = false;

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
        let mut v = Vec::with_capacity(8);
        for x in Adj::new(pos.0, pos.1) {
            if self.src.old_set[self.id_to_inside(x.0, x.1)] {
                v.push(x)
            }
        }
        v
    }
    fn is_old<Adj: AdjacentIterator>(&mut self) -> bool {
        if self.is_old_interior_up_to::<Adj>(self.src.rows as isize) {
            // don't know how to make borrow checker understand i don't mutate phases
            let iter = unsafe {
                let ptr = &self.phases as *const Vec<(isize, isize)>;
                (*ptr).iter()
            };
            for phase in iter {
                self.src.phase = *phase;
                if self.is_old_with_current_phase::<Adj>() {
                    return true;
                }
            }
        }
        false
    }
    fn try_satisfy<Adj: AdjacentIterator>(&mut self) -> Option<usize> {
        for x in &mut self.src.old_set { *x = false; }
        self.prevs.clear();
        if self.calc_old_min_interior::<Adj>(0) { Some(self.needed) } else { None }
    }
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
    fn size(&self) -> usize {
        self.old_set.len()
    }
    fn solver<Codes: CodeSet>(&mut self, thresh: f64) -> RectSolver<'_, Codes> {
        let needed = (self.old_set.len() as f64 * thresh).ceil() as usize - 1;
        let (r, c) = (self.rows, self.cols);
        RectSolver::<Codes> {
            src: self,
            phases: {
                let max_phase_x = (r as isize + 1) / 2;
                let max_phase_y = (c as isize + 1) / 2;
                std::iter::once((0, 0)).chain((1..=max_phase_x).map(|x| (x, 0))).chain((1..=max_phase_y).map(|y| (0, y))).collect()
            },
            codes: Default::default(),
            interior_codes: Default::default(),
            needed,
            prevs: Vec::with_capacity(needed),
        }
    }
}

enum GeometryLoadResult {
    FileOpenFailure,
    InvalidFormat(&'static str),
    TessellationFailure(&'static str),
}
struct GeometrySolver<'a, Codes> {
    shape: &'a BTreeSet<(isize, isize)>,
    shape_with_padding: &'a BTreeSet<(isize, isize)>,
    tessellation_map: &'a HashMap<(isize, isize), (isize, isize)>,
    old_set: &'a mut BTreeSet<(isize, isize)>,

    codes: Codes,
    needed: usize,
    prevs: Vec<(isize, isize)>,
}
impl<'a, Codes> GeometrySolver<'a, Codes>
where Codes: CodeSet
{
    fn calc_old_min_interior<'b, Adj, P>(&mut self, mut pos: P) -> bool
    where Adj: AdjacentIterator, P: Iterator<Item = &'b (isize, isize)> + Clone
    {
        if self.needed == self.prevs.len() {
            if self.is_old::<Adj>() {
                return true;
            }
        } else if let Some(&p) = pos.next() {
            self.old_set.insert(p);
            self.prevs.push(p);
            if self.calc_old_min_interior::<Adj, _>(pos.clone()) {
                return true;
            }
            self.prevs.pop();
            self.old_set.remove(&p);

            return self.calc_old_min_interior::<Adj, _>(pos);
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
    shape_with_padding: BTreeSet<(isize, isize)>,
    tessellation_map: HashMap<(isize, isize), (isize, isize)>,
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
            shape, shape_with_padding, tessellation_map,
            basis_a, basis_b,
            old_set: Default::default(),
        })
    }
    fn size(&self) -> usize {
        self.shape.len()
    }
    fn solver<Codes>(&mut self, thresh: f64) -> GeometrySolver<'_, Codes>
    where Codes: CodeSet
    {
        assert!(thresh > 0.0 && thresh <= 1.0);
        self.old_set.clear();

        let needed = (self.size() as f64 * thresh).ceil() as usize - 1;
        GeometrySolver::<Codes> {
            shape: &self.shape,
            shape_with_padding: &self.shape_with_padding,
            tessellation_map: &self.tessellation_map,
            old_set: &mut self.old_set,

            codes: Default::default(),
            needed,
            prevs: Vec::with_capacity(needed),
        }
    }
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
fn test_rect_pos() {
    let mut gg = RectTessellation::new(4, 4);
    let g = gg.solver::<OLDSet>(0.9);

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

fn main() {
    let v: Vec<String> = std::env::args().collect();
    if v.len() < 2 {
        eprintln!("usage: {} (rect|geo) (old|red|det) (full|rand) (args...)", v[0]);
        std::process::exit(1);
    }

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

    match v[1].as_str() {
        "rect" => {
            let (rows, cols) = {
                let rows: usize = v[2].parse().unwrap();
                let cols: usize = v[3].parse().unwrap();
                if rows >= cols { (rows, cols) } else { (cols, rows) }
            };
            if cols < 2 {
                eprintln!("1x1, 1xn, nx1 are not supported to avoid branch conditions\nthey also cannot result in lower than 2/3");
                std::process::exit(3);
            }
            let mut tess = RectTessellation::new(rows, cols);

            let thresh = parse_thresh(v[5].as_str());
            let res = match v[4].as_str() {
                "old:king" => tess.solver::<OLDSet>(thresh).try_satisfy::<Adjacent8>(),
                "det:king" => tess.solver::<DETSet>(thresh).try_satisfy::<Adjacent8>(),

                "old:tri" => tess.solver::<OLDSet>(thresh).try_satisfy::<AdjacentTriangle>(),
                "det:tri" => tess.solver::<DETSet>(thresh).try_satisfy::<AdjacentTriangle>(),

                _ => {
                    eprintln!("unknown type: {}", v[4]);
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
            };
        },
        "geo" => {
            let mut tess = match GeometryTessellation::with_shape(&v[2]) {
                Ok(x) => x,
                Err(e) => {
                    match e {
                        GeometryLoadResult::FileOpenFailure => eprintln!("failed to open tessellation file {}", v[2]),
                        GeometryLoadResult::InvalidFormat(msg) => eprintln!("file {} was invalid format: {}", v[2], msg),
                        GeometryLoadResult::TessellationFailure(msg) => eprintln!("file {} had a tessellation failure: {}", v[2], msg),
                    };
                    std::process::exit(5);
                },
            };

            let thresh = parse_thresh(v[4].as_str());
            let res = match v[3].as_str() {
                "old:king" => tess.solver::<OLDSet>(thresh).try_satisfy::<Adjacent8>(),
                "old:tri" => tess.solver::<OLDSet>(thresh).try_satisfy::<AdjacentTriangle>(),
                _ => {
                    eprintln!("unknown type: {}", v[3]);
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
            };
        },
        _ => {
            eprintln!("usage: {} (rect|geo) args...", v[0]);
            std::process::exit(2);
        }
    };
}

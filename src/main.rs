use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::io::{BufRead, BufReader};
use std::fs::File;
use std::path::Path;
use rand::Rng;

struct Adjacent {
    row: isize,
    col: isize,
    state: usize,
}
impl Adjacent {
    fn new(row: isize, col: isize) -> Self {
        Self { row, col, state: 0 }
    }
}
impl Iterator for Adjacent {
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
impl ExactSizeIterator for Adjacent {}

struct Adjacent4 {
    row: isize,
    col: isize,
    state: usize,
}
impl Adjacent4 {
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

struct SolverData {
    phases: Vec<(isize, isize)>,
    codes: BTreeSet<Vec<(isize, isize)>>,
    interior_codes: BTreeSet<Vec<(isize, isize)>>,
    needed: usize,
    prevs: Vec<(isize, isize)>,
}

struct KGridRect {
    rows: usize,
    cols: usize,
    old_set: Vec<bool>,
    phase: (isize, isize),
}
impl fmt::Display for KGridRect {
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
impl fmt::Debug for KGridRect {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let _r = self.rows as isize;
        let _c = self.cols as isize;

        for r in -1..=_r {
            for c in -1..=_c {
                let inside = self.id_to_inside(r, c);
                let v = if self.old_set[inside] { 1 } else { 0 };
                let code = self.get_locating_code(r, c);

                if r == -1 || r == _r || c == -1 || c == _c {
                    write!(f, "({}:{:?}) ", v, code)?;
                } else {
                    write!(f, "{}:{:?} ", v, code)?;
                }
            }
            writeln!(f)?;
        }
        writeln!(f, "phase: {:?}", self.phase)?;
        Ok(())
    }
}
impl KGridRect {
    fn new(rows: usize, cols: usize) -> Self {
        assert!(rows >= 2);
        assert!(cols >= 2);

        KGridRect {
            rows, cols,
            old_set: vec![false; rows * cols],
            phase: (0, 0),
        }
    }
    fn id_to_inside(&self, row: isize, col: isize) -> usize {
        let col_fix = if row < 0 { col - self.phase.0 } else if row >= self.rows as isize { col + self.phase.0 } else { col };
        let row_fix = if col < 0 { row - self.phase.1 } else if col >= self.cols as isize { row + self.phase.1 } else { row };

        let r = (row_fix + 2 * self.rows as isize) as usize % self.rows;
        let c = (col_fix + 2 * self.cols as isize) as usize % self.cols;
        r * self.cols + c
    }
    fn get_locating_code(&self, row: isize, col: isize) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(8);
        for x in Adjacent::new(row, col) {
            if self.old_set[self.id_to_inside(x.0, x.1)] {
                v.push(x)
            }
        }
        v.sort();
        v
    }
    fn is_old_with_current_phase(&self, codes: &mut BTreeSet<Vec<(isize, isize)>>, interior_codes: &BTreeSet<Vec<(isize, isize)>>) -> bool {
        codes.clear();
        for &r in &[-1, 0, self.rows as isize - 1, self.rows as isize] {
            for c in -1 ..= self.cols as isize {
                let code = self.get_locating_code(r, c);
                if code.is_empty() || interior_codes.contains(&code) || !codes.insert(code) {
                    return false;
                }
            }
        }
        for r in 1 ..= self.rows as isize - 2 {
            for &c in &[-1, 0, self.cols as isize - 1, self.cols as isize] {
                let code = self.get_locating_code(r, c);
                if code.is_empty() || interior_codes.contains(&code) || !codes.insert(code) {
                    return false;
                }
            }
        }
        true
    }
    fn is_old(&mut self, codes: &mut BTreeSet<Vec<(isize, isize)>>, interior_codes: &mut BTreeSet<Vec<(isize, isize)>>, phases: &[(isize, isize)]) -> bool {
        if self.is_old_interior_up_to(self.rows as isize, interior_codes) {
            for phase in phases {
                self.phase = *phase;
                if self.is_old_with_current_phase(codes, interior_codes) {
                    return true;
                }
            }
        }
        false
    }
    fn is_old_interior_up_to(&self, row: isize, codes: &mut BTreeSet<Vec<(isize, isize)>>) -> bool {
        codes.clear();
        for r in 1..row - 1 {
            for c in 1..self.cols as isize - 1 {
                let code = self.get_locating_code(r, c);
                if code.is_empty() || !codes.insert(code) {
                    return false;
                }
            }
        }
        true
    }
    fn calc_old_min(&mut self, thresh: f64) -> Option<usize> {
        assert!(thresh > 0.0 && thresh <= 1.0);
        assert_eq!(self.old_set.len(), self.rows * self.cols);
        for x in &mut self.old_set {
            *x = false;
        }

        let needed = (self.old_set.len() as f64 * thresh).ceil() as usize - 1;
        let mut data = SolverData {
            phases: {
                let max_phase_x = (self.cols as isize + 1) / 2;
                let max_phase_y = (self.rows as isize + 1) / 2;
                std::iter::once((0, 0)).chain((1..=max_phase_x).map(|x| (x, 0))).chain((1..=max_phase_y).map(|y| (0, y))).collect()
            },
            codes: Default::default(),
            interior_codes: Default::default(),
            needed,
            prevs: Vec::with_capacity(needed),
        };

        if self.calc_old_min_interior(&mut data, 0) { Some(needed) } else { None }
    }
    fn calc_old_min_interior(&mut self, data: &mut SolverData, pos: usize) -> bool {
        if data.needed == data.prevs.len() {
            if self.is_old(&mut data.codes, &mut data.interior_codes, &data.phases) {
                return true;
            }
        } else if pos < self.old_set.len() {
            let p = ((pos / self.cols) as isize, (pos % self.cols) as isize);

            let good_so_far = p.1 != 0 || self.is_old_interior_up_to(p.0, &mut data.codes);

            if good_so_far {
                self.old_set[pos] = true;
                data.prevs.push(p);
                if self.calc_old_min_interior(data, pos + 1) {
                    return true;
                }
                data.prevs.pop();
                self.old_set[pos] = false;

                return self.calc_old_min_interior(data, pos + 1);
            }
        }

        false
    }
}

#[derive(Debug)]
enum GeometryLoadResult {
    FileOpenFailure,
    InvalidFormat,
    TessellationFailure,
}
struct FancySolverData<'a> {
    codes: BTreeSet<Vec<(isize, isize)>>,
    needed: usize,
    prevs: Vec<(isize, isize)>,

    old_set: &'a mut BTreeSet<(isize, isize)>,
    shape_with_padding: &'a BTreeSet<(isize, isize)>,
    tessellation_map: &'a HashMap<(isize, isize), (isize, isize)>,
}
impl<'a> FancySolverData<'a> {
    fn get_locating_code(&self, pos: (isize, isize)) -> Vec<(isize, isize)> {
        let mut v = Vec::with_capacity(8);
        for x in Adjacent::new(pos.0, pos.1) {
            let mapped = self.tessellation_map.get(&x).unwrap();
            if self.old_set.contains(mapped) {
                v.push(x);
            }
        }
        v
    }
    fn is_old(&mut self) -> bool {
        self.codes.clear();
        for pos in self.shape_with_padding {
            let code = self.get_locating_code(*pos);
            if code.is_empty() || !self.codes.insert(code) {
                return false;
            }
        }
        true
    }
    fn calc_old_min_interior<'b, P>(&mut self, mut pos: P) -> bool
    where P: Iterator<Item = &'b (isize, isize)> + Clone
    {
        if self.needed == self.prevs.len() {
            if self.is_old() {
                return true;
            }
        } else if let Some(&p) = pos.next() {
            self.old_set.insert(p);
            self.prevs.push(p);
            if self.calc_old_min_interior(pos.clone()) {
                return true;
            }
            self.prevs.pop();
            self.old_set.remove(&p);

            return self.calc_old_min_interior(pos);
        }

        false
    }
}
struct KGridFancyTessellation {
    shape: BTreeSet<(isize, isize)>,
    shape_with_padding: BTreeSet<(isize, isize)>,
    tessellation_map: HashMap<(isize, isize), (isize, isize)>,
    old_set: BTreeSet<(isize, isize)>,
}
impl fmt::Display for KGridFancyTessellation {
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
        Ok(())
    }
}
impl KGridFancyTessellation {
    fn with_shape<P: AsRef<Path>>(path: P) -> Result<Self, GeometryLoadResult> {
        let mut f = BufReader::new(match File::open(path) {
            Ok(x) => x,
            Err(_) => return Err(GeometryLoadResult::FileOpenFailure),
        });

        let (tess_a, tess_b) = {
            let mut line = String::new();
            f.read_line(&mut line).unwrap();

            let args: Vec<&str> = line.split_whitespace().collect();
            if args.len() != 4 {
                return Err(GeometryLoadResult::InvalidFormat);
            }
            let mut parsed: Vec<isize> = vec![];
            for arg in args {
                parsed.push(match arg.parse::<isize>() {
                    Ok(x) => x,
                    Err(_) => return Err(GeometryLoadResult::InvalidFormat),
                });
            }
            ((parsed[0], parsed[1]), (parsed[2], parsed[3]))
        };

        let shape = {
            let mut shape: BTreeSet<(isize, isize)> = Default::default();
            for (row, line) in f.lines().map(|x| x.unwrap()).enumerate() {
                for (col, item) in line.split_whitespace().enumerate() {
                    match item.parse::<u8>() {
                        Ok(x) if x <= 1 => {
                            if x != 0 {
                                shape.insert((row as isize, col as isize));
                            }
                        },
                        _ => return Err(GeometryLoadResult::InvalidFormat),
                    };
                }
            }
            if shape.is_empty() {
                return Err(GeometryLoadResult::InvalidFormat);
            }
            shape
        };

        let shape_with_padding: BTreeSet<_> = {
            shape.clone().into_iter().flat_map(|x| Adjacent::new(x.0, x.1)).collect()
        };
        let shape_with_extra_padding: BTreeSet<_> = {
            shape_with_padding.clone().into_iter().flat_map(|x| Adjacent::new(x.0, x.1)).collect()
        };

        let tessellation_map = {
            let mut p: HashSet<(isize, isize)> = HashSet::with_capacity(shape.len() * 25);
            let mut m: HashMap<(isize, isize), (isize, isize)> = HashMap::with_capacity(shape.len() * 9);

            for &to in &shape {
                for i in -2..=2 {
                    for j in -2..=2 {
                        let from = (to.0 + tess_a.0 * i + tess_b.0 * j, to.1 + tess_a.1 * i + tess_b.1 * j);
                        if !p.insert(from) {
                            return Err(GeometryLoadResult::TessellationFailure);
                        }
                        if shape_with_extra_padding.contains(&from) {
                            m.insert(from, to);
                        }
                    }
                }
            }
            for pos in &shape_with_extra_padding {
                if !m.contains_key(pos) {
                    return Err(GeometryLoadResult::TessellationFailure);
                }
            }

            m
        };

        Ok(Self {
            shape, shape_with_padding, tessellation_map,
            old_set: Default::default(),
        })
    }
    fn size(&self) -> usize {
        self.shape.len()
    }

    fn calc_old_min(&mut self, thresh: f64) -> Option<usize> {
        assert!(thresh > 0.0 && thresh <= 1.0);
        self.old_set.clear();

        let needed = (self.size() as f64 * thresh).ceil() as usize - 1;
        let mut data = FancySolverData {
            codes: Default::default(),
            needed,
            prevs: Vec::with_capacity(needed),

            old_set: &mut self.old_set,
            tessellation_map: &self.tessellation_map,
            shape_with_padding: &self.shape_with_padding
        };

        if data.calc_old_min_interior(self.shape.iter()) { Some(needed) } else { None }
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

fn main() {
    let v: Vec<String> = std::env::args().collect();
    if v.len() < 2 {
        eprintln!("usage: {} [mode] (args...)", v[0]);
        std::process::exit(1);
    }

    {
        let mut g = KGridRect::new(4, 4);

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

        g.phase = (1, 0);

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

        g.phase = (0, 1);

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
        "full" => {
            if v.len() != 5 {
                eprintln!("usage: {} full [rows] [cols] [thresh]", v[0]);
                std::process::exit(2);
            }

            let (rows, cols) = {
                let rows: usize = v[2].parse().unwrap();
                let cols: usize = v[3].parse().unwrap();
                if rows >= cols { (rows, cols) } else { (cols, rows) }
            };
            if cols < 2 {
                eprintln!("1x1, 1xn, nx1 are not supported to avoid branch conditions\nthey also cannot result in lower than 2/3");
                std::process::exit(3);
            }
            let thresh = parse_thresh(v[4].as_str());

            let mut grid = KGridRect::new(rows, cols);
            match grid.calc_old_min(thresh) {
                Some(min) => {
                    let n = rows * cols;
                    let d = gcd(min, n);
                    println!("NEW BEST!! {}/{} ({}):\n{}", (min / d), (n / d), (min as f64 / n as f64), grid);
                },
                None => println!("not better than {}", thresh),
            };
        },
        "geo" => {
            if v.len() != 4 {
                eprintln!("usage: {} geo [geometry file] [thresh]", v[0]);
                std::process::exit(2);
            }

            let mut geo = match KGridFancyTessellation::with_shape(&v[2]) {
                Ok(x) => x,
                Err(e) => {
                    eprintln!("failed to load tessellation file {} ({:?})", v[2], e);
                    std::process::exit(5);
                },
            };
            let thresh = parse_thresh(v[3].as_str());

            match geo.calc_old_min(thresh) {
                Some(min) => {
                    let n = geo.size();
                    let d = gcd(min, n);
                    println!("NEW BEST!! {}/{} ({}):\n{}", (min / d), (n / d), (min as f64 / n as f64), geo);
                },
                None => println!("not better than {}", thresh),
            };
        },
        "rand" => {
            if v.len() != 5 {
                eprintln!("usage: {} rand [rows] [cols] [thesh]", v[0]);
                std::process::exit(2);
            }

            let rows: usize = v[2].parse().unwrap();
            let cols: usize = v[3].parse().unwrap();
            if rows < 2 || cols < 2 {
                eprintln!("1x1, 1xn, nx1 are not supported to avoid branch conditions\nthey also cannot result in lower than 2/3");
                std::process::exit(3);
            }
            let thresh = parse_thresh(v[4].as_str());

            let mut grid = KGridRect::new(rows, cols);

            let n: usize = rows * cols;
            let k: usize = (n as f64 * thresh).ceil() as usize - 1;
            assert!(n > k);

            let max_phase_x: isize = (cols as isize + 1) / 2;
            let max_phase_y: isize = (rows as isize + 1) / 2;
            let phases: Vec<_> = std::iter::once((0, 0)).chain((1..=max_phase_x).map(|x| (x, 0))).chain((1..=max_phase_y).map(|x| (0, x))).collect();

            let mut rng = rand::thread_rng();
            let mut codes = Default::default();
            let mut interior_codes = Default::default();
            for i in 0usize.. {
                for x in &mut grid.old_set { *x = false; }
                for _ in 0..k {
                    loop {
                        let p: usize = rng.gen_range(0, n);
                        if !grid.old_set[p] {
                            grid.old_set[p] = true;
                            break;
                        }
                    }
                }

                if grid.is_old(&mut codes, &mut interior_codes, &phases) {
                    let d = gcd(n, k);
                    println!("NEW BEST!! {}/{} ({})\n{}", (k / d), (n / d), (k as f64 / n as f64), grid);
                    break;
                }

                if i % 65536 == 0 {
                    println!("rand iterations: {}\n{}", i, grid);
                }
            }
        },
        _ => {
            eprintln!("usage: {} [mode] (args...)", v[0]);
            std::process::exit(1);
        },
    }
}

use std::collections::BTreeSet;
use std::fmt;

use rand::Rng;

const CURRENT_BEST: f64 = 0.25;

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

struct KGrid {
    rows: usize,
    cols: usize,
    old_set: Vec<bool>,
    phase: (isize, isize),
}
struct SolverData {
    phases: Vec<(isize, isize)>,
    codes: BTreeSet<Vec<(isize, isize)>>,
    interior_codes: BTreeSet<Vec<(isize, isize)>>,
    needed: usize,
    prevs: Vec<(isize, isize)>,
}
impl fmt::Display for KGrid {
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
impl fmt::Debug for KGrid {
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
impl KGrid {
    fn new(rows: usize, cols: usize) -> Self {
        assert_ne!(rows, 0);
        assert_ne!(cols, 0);

        KGrid {
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
    fn calc_old_min(&mut self) -> Option<usize> {
        assert_eq!(self.old_set.len(), self.rows * self.cols);
        for x in &mut self.old_set {
            *x = false;
        }

        let needed = (self.old_set.len() as f64 * CURRENT_BEST).ceil() as usize - 1;
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

        if self.calc_old_min_interior(&mut data, 0) { Some(data.needed) } else { None }
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
        let mut g = KGrid::new(4, 4);

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

    match v[1].as_str() {
        "full" => {
            if v.len() != 4 {
                eprintln!("usage: {} full [rows] [cols]", v[0]);
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

            let mut grid = KGrid::new(rows, cols);
            match grid.calc_old_min() {
                Some(min) => {
                    let n = rows * cols;
                    let d = gcd(min, n);
                    println!("NEW BEST!! {}/{} ({}):\n{}", (min / d), (n / d), (min as f64 / n as f64), grid);
                },
                None => {
                    println!("not better than {}", CURRENT_BEST);
                }
            };
        },
        "rand" => {
            if v.len() != 4 {
                eprintln!("usage: {} rand [rows] [cols]", v[0]);
                std::process::exit(2);
            }

            let rows: usize = v[2].parse().unwrap();
            let cols: usize = v[3].parse().unwrap();
            if rows < 2 || cols < 2 {
                eprintln!("1x1, 1xn, nx1 are not supported to avoid branch conditions\nthey also cannot result in lower than 2/3");
                std::process::exit(3);
            }

            let mut grid = KGrid::new(rows, cols);

            let n: usize = rows * cols;
            let k: usize = (n as f64 * CURRENT_BEST).ceil() as usize - 1;
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

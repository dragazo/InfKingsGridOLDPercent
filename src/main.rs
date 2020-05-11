use std::collections::BTreeSet;
use std::fmt;

use itertools::Itertools;
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
            0 => (r, c - 1),
            1 => (r, c + 1),

            2 => (r - 1, c),
            3 => (r + 1, c),

            4 => (r - 1, c - 1),
            5 => (r - 1, c + 1),

            6 => (r + 1, c - 1),
            7 => (r + 1, c + 1),

            _ => return None,
        };
        self.state += 1;
        Some(v)
    }
}

struct KGrid {
    rows: usize,
    cols: usize,
    old_set: Vec<bool>,
}
impl fmt::Display for KGrid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for r in 0..self.rows {
            for c in 0..self.cols {
                write!(f, "{} ", if self.old_set[r * self.cols + c] { 1 } else { 0 })?;
            }
            writeln!(f)?;
        }
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
        }
    }
    fn set_size(&mut self, rows: usize, cols: usize) {
        assert_ne!(rows, 0);
        assert_ne!(cols, 0);

        self.rows = rows;
        self.cols = cols;
        self.old_set.clear();
        self.old_set.extend(std::iter::once(false).cycle().take(rows * cols));
    }
    fn id_to_inside(&self, row: isize, col: isize) -> usize {
        let r = (row + self.rows as isize) as usize % self.rows;
        let c = (col + self.cols as isize) as usize % self.cols;
        r * self.cols + c
    }
    fn get_locating_code(&self, row: isize, col: isize) -> Vec<(isize, isize)> {
        let mut v: Vec<_> = Adjacent::new(row, col).filter(|x| self.old_set[self.id_to_inside(x.0, x.1)]).collect();
        v.sort();
        v
    }
    fn is_old(&self, codes: &mut BTreeSet<Vec<(isize, isize)>>) -> bool {
        codes.clear();
        for r in -1..=self.rows as isize {
            for c in -1..=self.cols as isize {
                let code = self.get_locating_code(r, c);
                if code.is_empty() || !codes.insert(code) {
                    return false;
                }
            }
        }
        true
    }
    fn calc_old_min<F>(&mut self, mut f: F) -> Option<usize>
    where F: FnMut(usize, &Self)
    {
        let n = self.rows * self.cols;
        assert_ne!(n, 0);

        let mut codes: BTreeSet<Vec<(isize, isize)>> = Default::default();
        let mut best: Option<usize> = None;

        for size in (1..(n as f64 * CURRENT_BEST).ceil() as usize).rev() {
            let mut works = false;
            for combo in (0..n).combinations(size) {
                for x in &mut self.old_set { *x = false; }
                for x in combo { self.old_set[x] = true; }
                if self.is_old(&mut codes) {
                    best = Some(size);
                    works = true;
                    f(size, self);
                    break;
                }
            }
            if !works { break; }
        }
        
        best
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

    match v[1].as_str() {
        "full" => {
            if v.len() != 4 {
                eprintln!("usage: {} full [rows] [cols]", v[0]);
                std::process::exit(2);
            }

            let rows: usize = v[2].parse().unwrap();
            let cols: usize = v[3].parse().unwrap();
            let mut grid = KGrid::new(rows, cols);

            let printer = |size: usize, g: &KGrid| {
                println!("worked for {}:\n{}", size, g);
            };
            match grid.calc_old_min(printer)
            {
                Some(min) => {
                    let n = rows * cols;
                    let d = gcd(min, n);
                    println!("NEW BEST!! {}/{} ({})", (min / d), (n / d), (min as f64 / n as f64));
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
            let mut grid = KGrid::new(rows, cols);

            let n: usize = rows * cols;
            let k: usize = (n as f64 * CURRENT_BEST).ceil() as usize - 1;
            assert!(n > k);

            let mut rng = rand::thread_rng();
            let mut codes = Default::default();
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

                if grid.is_old(&mut codes) {
                    let d = gcd(n, k);
                    println!("NEW BEST!! {}/{} ({}) (from rand exec, so could be even better - retest with new upper bound)\n{}",
                        (k / d), (n / d), (k as f64 / n as f64), grid);
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

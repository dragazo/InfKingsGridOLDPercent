use std::collections::BTreeSet;
use std::fmt;
use itertools::Itertools;

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
    fn new() -> Self {
        KGrid {
            rows: 0,
            cols: 0,
            old_set: vec![],
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
    fn calc_old_min(&mut self) -> usize {
        let mut codes: BTreeSet<Vec<(isize, isize)>> = BTreeSet::new();
        let n = self.rows * self.cols;
        assert_ne!(n, 0);

        for size in 1..=n {
            for combo in (0..n).combinations(size) {
                for x in &mut self.old_set {
                    *x = false;
                }
                for x in combo {
                    self.old_set[x] = true;
                }
                codes.clear();
                let mut valid = true;
                for r in -1..=self.rows as isize {
                    for c in -1..=self.cols as isize {
                        let code = self.get_locating_code(r, c);
                        if code.is_empty() || !codes.insert(code) {
                            valid = false;
                            break;
                        }
                    }
                    if !valid { break; }
                }
                if valid { return size; }
            }
        }
        unreachable!();
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
    if v.len() != 3 {
        eprintln!("usage: {} [rows] [cols]", v[0]);
        std::process::exit(1);
    }

    #[cfg(debug_assertions)]
    {
        let mut grid = KGrid::new();
        grid.set_size(4, 4);

        assert_eq!(grid.id_to_inside(0, 0), 0);
        assert_eq!(grid.id_to_inside(1, 0), 4);
        assert_eq!(grid.id_to_inside(2, 1), 9);
        assert_eq!(grid.id_to_inside(0, -1), 3);
        assert_eq!(grid.id_to_inside(-1, 2), 14);
        assert_eq!(grid.id_to_inside(4, 1), 1);
    }

    let rows: usize = v[1].parse().unwrap();
    let cols: usize = v[2].parse().unwrap();

    let mut grid = KGrid::new();
    grid.set_size(rows, cols);

    let min = grid.calc_old_min();
    let n = rows * cols;
    let d = gcd(min, n);
    println!("{}/{} ({})\n{}\n{:?}", min / d, n / d, (min as f64 / n as f64), grid, grid);
}

#[derive(Clone)]
pub struct PointMap<T> {
    data: Vec<Option<T>>,

    top: isize,
    bottom: isize,
    left: isize,
    right: isize,

    cols: isize,
}
impl<T> PointMap<T> {
    pub fn with_bounds(a: (isize, isize), b: (isize, isize)) -> Self {
        let (top, bottom) = if a.0 <= b.0 { (a.0, b.0) } else { (b.0, a.0) };
        let (left, right) = if a.1 <= b.1 { (a.1, b.1) } else { (b.1, a.1) };

        let rows = bottom - top + 1;
        let cols = right - left + 1;
        let size = (rows * cols) as usize;
        
        let mut data: Vec<_> = Vec::with_capacity(size);
        for _ in 0..size {
            data.push(None);
        }

        Self {
            data,
            top, bottom, left, right,
            cols,
        }
    }
    pub fn clear(&mut self) {
        for i in self.data.iter_mut() {
            *i = None;
        }
    }

    fn get_pos(&self, val: (isize, isize)) -> usize {
        assert!(val.0 >= self.top && val.0 <= self.bottom && val.1 >= self.left && val.1 <= self.right);
        ((val.0 - self.top) * self.cols + (val.1 - self.left)) as usize
    }
    pub fn insert(&mut self, key: (isize, isize), value: T) {
        let pos = self.get_pos(key);
        self.data[pos] = Some(value);
    }
    pub fn remove(&mut self, key: &(isize, isize)) {
        let pos = self.get_pos(*key);
        self.data[pos] = None;
    }
    pub fn contains_key(&self, key: &(isize, isize)) -> bool {
        let pos = self.get_pos(*key);
        self.data[pos].is_some()
    }
    pub fn get(&self, key: &(isize, isize)) -> Option<&T> {
        let pos = self.get_pos(*key);
        self.data[pos].as_ref()
    }

    pub fn iter(&self) -> impl Iterator<Item = ((isize, isize), &T)> + Clone {
        let (top, bottom, left, right) = (self.top, self.bottom, self.left, self.right);
        (top..=bottom).flat_map(move |r| (left..=right).map(move |c| (r, c))).zip(self.data.iter()).filter_map(|(k, v)| Some((k, v.as_ref()?)))
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = ((isize, isize), &mut T)> {
        let (top, bottom, left, right) = (self.top, self.bottom, self.left, self.right);
        (top..=bottom).flat_map(move |r| (left..=right).map(move |c| (r, c))).zip(self.data.iter_mut()).filter_map(|(k, v)| Some((k, v.as_mut()?)))
    }
}
impl<T> Extend<((isize, isize), T)> for PointMap<T> {
    fn extend<I>(&mut self, iter: I)
    where I: IntoIterator<Item = ((isize, isize), T)>
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

#[derive(Clone)]
pub struct PointSet {
    w: PointMap<()>,
}
impl PointSet {
    pub fn with_bounds(a: (isize, isize), b: (isize, isize)) -> Self {
        Self { w: PointMap::with_bounds(a, b) }
    }
    pub fn clear(&mut self) {
        self.w.clear()
    }

    pub fn insert(&mut self, value: (isize, isize)) {
        self.w.insert(value, ())
    }
    pub fn remove(&mut self, value: &(isize, isize)) {
        self.w.remove(value)
    }
    pub fn contains(&self, value: &(isize, isize)) -> bool {
        self.w.contains_key(value)
    }

    pub fn iter(&self) -> impl Iterator<Item = (isize, isize)> + '_ + Clone {
        self.w.iter().map(|(k, _)| k)
    }
}
impl Extend<(isize, isize)> for PointSet {
    fn extend<I>(&mut self, iter: I)
    where I: IntoIterator<Item = (isize, isize)>
    {
        for x in iter {
            self.insert(x);
        }
    }
}

#[test]
fn test_point_map() {
    let mut s = PointMap::<i32>::with_bounds((-3, -4), (1, 2));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![]);

    let mut idx = 0;
    for row in -3..=1 {
        for col in -4..=2 {
            assert_eq!(s.get_pos((row, col)), idx);
            idx += 1;
        }
    }

    assert!(!s.contains_key(&(0, 1)));
    s.insert((0, 1), -534);
    assert!(s.contains_key(&(0, 1)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![((0, 1), &-534)]);
    assert_eq!(s.iter_mut().collect::<Vec<_>>(), vec![((0, 1), &mut -534)]);

    assert!(!s.contains_key(&(-1, -3)));
    s.insert((-1, -3), 10243);
    assert!(s.contains_key(&(-1, -3)));
    assert!(s.contains_key(&(0, 1)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![((-1, -3), &10243), ((0, 1), &-534)]);
    assert_eq!(s.iter_mut().collect::<Vec<_>>(), vec![((-1, -3), &mut 10243), ((0, 1), &mut -534)]);

    for (_, v) in s.iter_mut() {
        *v += 10;
    }
    assert!(s.contains_key(&(-1, -3)));
    assert!(s.contains_key(&(0, 1)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![((-1, -3), &10253), ((0, 1), &-524)]);
    assert_eq!(s.iter_mut().collect::<Vec<_>>(), vec![((-1, -3), &mut 10253), ((0, 1), &mut -524)]);

    s.remove(&(0, 1));
    assert!(!s.contains_key(&(0, 1)));
    assert!(s.contains_key(&(-1, -3)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![((-1, -3), &10253)]);
    assert_eq!(s.iter_mut().collect::<Vec<_>>(), vec![((-1, -3), &mut 10253)]);

    s.clear();
    assert!(!s.contains_key(&(0, 1)));
    assert!(!s.contains_key(&(-1, -3)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![]);
    assert_eq!(s.iter_mut().collect::<Vec<_>>(), vec![]);

    s.extend(vec![((1, 1), 453), ((1, 0), 444), ((1, 2), 234)]);
    assert!(s.contains_key(&(1, 1)));
    assert!(s.contains_key(&(1, 2)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![((1, 0), &444), ((1, 1), &453), ((1, 2), &234)]);
    assert_eq!(s.iter_mut().collect::<Vec<_>>(), vec![((1, 0), &mut 444), ((1, 1), &mut 453), ((1, 2), &mut 234)]);
}

#[test]
fn test_point_set() {
    let mut s = PointSet::with_bounds((-3, -4), (1, 2));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![]);

    assert!(!s.contains(&(0, 1)));
    s.insert((0, 1));
    assert!(s.contains(&(0, 1)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![(0, 1)]);

    assert!(!s.contains(&(-1, -3)));
    s.insert((-1, -3));
    assert!(s.contains(&(-1, -3)));
    assert!(s.contains(&(0, 1)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![(-1, -3), (0, 1)]);

    s.remove(&(0, 1));
    assert!(!s.contains(&(0, 1)));
    assert!(s.contains(&(-1, -3)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![(-1, -3)]);

    s.clear();
    assert!(!s.contains(&(0, 1)));
    assert!(!s.contains(&(-1, -3)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![]);

    s.extend(vec![(1, 1), (1, 0), (1, 2)]);
    assert!(s.contains(&(1, 1)));
    assert!(s.contains(&(1, 2)));
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![(1, 0), (1, 1), (1, 2)]);
}
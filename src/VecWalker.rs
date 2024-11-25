pub struct VecWalker<'a, T: 'a> {
    vec: &'a Vec<T>,
    index: usize,
}

impl<'a, T> VecWalker<'a, T> {
    /// Creates a new VecWalker.
    pub fn new(vec: &'a Vec<T>) -> Self {
        Self { vec, index: 0 }
    }

    /// Moves forward in the vector and returns the next element, if available.
    pub fn next(&mut self) -> Option<&T> {
        if self.index < self.vec.len() {
            let item = &self.vec[self.index];
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }

    pub fn peek(&mut self) -> Option<&T> {
        if self.index < self.vec.len() {
            Some(&self.vec[self.index])
        } else {
            None
        }
    }


    /// Moves backward in the vector and returns the previous element, if available.
    pub fn previous(&mut self) -> Option<&T> {
        if self.index > 0 {
            self.index -= 1;
            Some(&self.vec[self.index])
        } else {
            None
        }
    }
}

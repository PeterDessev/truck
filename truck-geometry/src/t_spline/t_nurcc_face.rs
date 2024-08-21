use super::*;

impl<P> Drop for TnurccFace<P> {
    fn drop(&mut self) {
        for i in 0..self.corners.len() {
            self.corners[i] = None;
        }
    }
}
use super::*;

impl<P> TnurccControlPoint<P> {
    /// Createss a new `TnurccControlPoint` instance with index `index`, cartesian point `point`,
    /// valence `0`, and no incoming edge (`None`).
    pub fn new(index: usize, point: P) -> Self {
        return TnurccControlPoint {
            index,
            valence: 0,
            point,
            incoming_edge: None,
        };
    }
}

impl<P> Drop for TnurccControlPoint<P> {
    fn drop(&mut self) {
        self.incoming_edge = None;
    }
}
use super::*;

impl<P> TnurccAcwPointIter<P> {
    /// Creates a new `TnurccAcwPointIter` which iterates the edges around `e`'s vertex `end` in an anti-clockwise manner.
    /// Returns `None` without making a full rotation, that is, will return `e` as the first element, but not the last.
    ///
    /// # Borrows
    /// Immutably borrows every edge connected to the point at `e`'s `end` when calling `next`.
    pub fn from_edge(e: Rc<RefCell<TnurccEdge<P>>>, end: TnurccVertexEnd) -> Self {
        return TnurccAcwPointIter {
            point: Rc::clone(&e.borrow().point_at_end(end)),
            start: Rc::clone(&e),
            cur: Some(Rc::clone(&e)),
        };
    }
}

impl<P> TnurccAcwFaceIter<P> {
    /// Creates a new `TnurccAcwFaceIter` which iterates the edges around `e`'s face `side` in an anti-clockwise manner.
    /// `next` returns `None` without making a full rotation, that is, will return `e` as the first element, but not the last.
    ///
    /// # Returns
    /// - `None` if `e` does not have a face on `side`.
    ///
    /// - `Some(iter)` otherwise.
    pub fn try_from_edge(e: Rc<RefCell<TnurccEdge<P>>>, side: TnurccFaceSide) -> Option<Self> {
        if let Some(face) = e.borrow().face_from_side(side) {
            Some(TnurccAcwFaceIter {
                face,
                start: Rc::clone(&e),
                cur: Some(Rc::clone(&e)),
            })
        } else {
            None
        }
    }

    /// Creates a new `TnurccAcwFaceIter` which iterates the edges around `f` in an anti-clockwise manner.
    /// `next` returns `None` without making a full rotation, that is, will not return the first edge twice.
    ///
    /// # Returns
    /// - `None` if `f` does not have a reference edge.
    ///
    /// - `Some(iter)` otherwise.
    #[allow(dead_code)]
    pub fn try_from_face(f: Rc<RefCell<TnurccFace<P>>>) -> Option<Self> {
        if let Some(edge) = f.borrow().edge.as_ref() {
            Some(TnurccAcwFaceIter {
                face: Rc::clone(&f),
                start: Rc::clone(edge),
                cur: Some(Rc::clone(edge)),
            })
        } else {
            None
        }
    }
}

impl<P> Iterator for TnurccAcwPointIter<P> {
    type Item = Rc<RefCell<TnurccEdge<P>>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.cur.as_ref().map(|r| Rc::clone(r));

        if let Some(edge) = self.cur.as_ref() {
            // Is point the origin or dest?
            let end = edge.borrow().point_end(Rc::clone(&self.point));

            if end.is_none() {
                return None;
            }
            let end = end.unwrap();

            // Get the next ACW edge for point
            let new_edge = edge.borrow().acw_edge_from_end(end);

            // If the new edge is the starting edge, stop the iterator by setting cur to none
            // Otherwise, keep going
            if std::ptr::eq(self.start.as_ref(), new_edge.as_ref()) {
                self.cur = None;
            } else {
                self.cur = Some(new_edge);
            }
        } else {
            return None;
        }

        return ret;
    }
}

impl<P> Iterator for TnurccAcwFaceIter<P> {
    type Item = Rc<RefCell<TnurccEdge<P>>>;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.cur.as_ref().map(|r| Rc::clone(r));

        if let Some(edge) = self.cur.as_ref() {
            // Is point the origin or dest?
            let side = edge.borrow().face_side(Rc::clone(&self.face));

            if side.is_none() {
                return None;
            }
            let side = side.unwrap();

            // Get the next ACW edge for point
            let new_edge = edge.borrow().acw_edge_from_side(side);

            // If the new edge is the starting edge, stop the iterator by setting cur to none
            // Otherwise, keep going
            if std::ptr::eq(self.start.as_ref(), new_edge.as_ref()) {
                self.cur = None;
            } else {
                self.cur = Some(new_edge);
            }
        } else {
            return None;
        }

        return ret;
    }
}

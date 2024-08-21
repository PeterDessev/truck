use super::*;

impl<P> TnurccAcwPointIter<P> {
    /// Creates a new `TnurccAcwPointIter` which iterates the edges around `e`'s vertex `end` in an anti-clockwise manner. 
    /// Returns `None` without making a full rotation, that is, will return `e` as the first element, but not the last.
    pub fn from_edge(e: Rc<RefCell<TnurccEdge<P>>>, end: TnurccVertexEnd) -> Self {
        return TnurccAcwPointIter {
            point: Rc::clone(&e.borrow().get_point(end)),
            start: Rc::clone(&e),
            cur: Some(Rc::clone(&e)),
        };
    }
}

impl<P> TnurccAcwFaceIter<P> {
    /// Creates a new `TnurccAcwFaceIter` which iterates the edges around `e`'s face `side` in an anti-clockwise manner. 
    /// Returns `None` without making a full rotation, that is, will return `e` as the first element, but not the last.
    pub fn try_from_edge(e: Rc<RefCell<TnurccEdge<P>>>, side: TnurccFaceSide) -> Option<Self> {
        if let Some(face) = e.borrow().get_face(side) {
            Some(TnurccAcwFaceIter {
                face,
                start: Rc::clone(&e),
                cur: Some(Rc::clone(&e)),
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
            let end = edge.borrow().get_point_side(Rc::clone(&self.point));

            if end.is_none() {
                return None;
            }
            let end = end.unwrap();

            // Get the next ACW edge for point
            let new_edge = edge.borrow().acw_edge_from_point(end);

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
            let side = edge.borrow().get_face_side(Rc::clone(&self.face));

            if side.is_none() {
                return None;
            }
            let side = side.unwrap();

            // Get the next ACW edge for point
            let new_edge = edge.borrow().acw_edge_from_face(side);

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

use super::*;

impl<P> TnurccFace<P> {
    /// Returns a vector containing all the points defining the boundry of the current face, in an
    /// anti-clockwise order starting from the origin of `f`'s reference edge. Returns an empty vector
    /// if `f` does not have a reference `edge`.
    ///
    /// # Panics
    /// Panics if `f`'s reference `edge` does not reference `f` as a face on either side.
    pub fn get_boundry_verticies(f: Rc<RefCell<Self>>) -> Vec<Rc<RefCell<TnurccControlPoint<P>>>> {
        if let Some(edge) = f.borrow().edge.as_ref().map(|r| Rc::clone(r)) {
            let face_side = edge
                .borrow()
                .get_face_side(Rc::clone(&f))
                .expect("Face edge should be on either side of that edge.");
            let iter = TnurccAcwFaceIter::try_from_edge(Rc::clone(&edge), face_side)
                .expect("Edge should have face on side if get_face_side succeeded");

            iter.map(|e| {
                match e
                    .borrow()
                    .get_face_side(Rc::clone(&f))
                    .expect("Edge on perimeter of face should be connected to the face")
                {
                    TnurccFaceSide::Left => Rc::clone(&e.borrow().origin),
                    TnurccFaceSide::Right => Rc::clone(&e.borrow().dest),
                }
            })
            .collect()
        } else {
            Vec::new()
        }
    }

    /// Returns a vector containing all the edges defining the border of the current face, in an
    /// anti-clockwise order starting from `f`'s reference edge. Returns an empty vector if `f`
    /// does not have a reference `edge`.
    ///
    /// # Panics
    /// Panics if `f`'s reference `edge` does not reference `f` as a face on either side.
    pub fn get_border_edges(f: Rc<RefCell<Self>>) -> Vec<Rc<RefCell<TnurccEdge<P>>>> {
        if let Some(edge) = f.borrow().edge.as_ref().map(|r| Rc::clone(r)) {
            let face_side = edge
                .borrow()
                .get_face_side(Rc::clone(&f))
                .expect("Face edge should be on either side of that edge.");
            let iter = TnurccAcwFaceIter::try_from_edge(Rc::clone(&edge), face_side)
                .expect("Edge should have face on side if get_face_side succeeded");

            iter.collect()
        } else {
            Vec::new()
        }
    }
}

impl<P> Drop for TnurccFace<P> {
    fn drop(&mut self) {
        for i in 0..self.corners.len() {
            self.corners[i] = None;
        }
        self.edge = None;
    }
}

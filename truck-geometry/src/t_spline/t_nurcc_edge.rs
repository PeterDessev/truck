use super::*;
use std::fmt;

impl<P> TnurccEdge<P> {
    /// Creates a new edge with index `index` and knot interval `knot_interval`, spanning
    /// from `origin` to `dest`. All connections will be to itself, and faces will be set to `None`.
    pub fn new(
        index: usize,
        knot_interval: f64,
        origin: Rc<RefCell<TnurccControlPoint<P>>>,
        dest: Rc<RefCell<TnurccControlPoint<P>>>,
    ) -> Rc<RefCell<Self>> {
        let edge = TnurccEdge {
            index,
            connections: [const { None }; 4],
            face_left: None,
            face_right: None,
            origin: Rc::clone(&origin),
            dest: Rc::clone(&dest),
            knot_interval,
        };
        let edge: Rc<RefCell<TnurccEdge<P>>> = Rc::new(RefCell::new(edge));

        origin.borrow_mut().valence += 1;
        origin.borrow_mut().incoming_edge = Some(Rc::clone(&edge));
        dest.borrow_mut().valence += 1;
        dest.borrow_mut().incoming_edge = Some(Rc::clone(&edge));

        edge.borrow_mut()
            .connections
            .fill_with(|| Some(Rc::clone(&edge)));

        return edge;
    }

    /// Returns the connected edge.
    ///
    /// # Panics
    /// Panics if `self` was not correctly initialized or was mangled, resulting in a `None` connection.
    pub fn connection(&self, con: TnurccConnection) -> Rc<RefCell<TnurccEdge<P>>> {
        return Rc::clone(
            self.connections[con as usize]
                .as_ref()
                .expect("TnurccEdge should always have a Some(connection)"),
        );
    }

    /// Replaces the connection `con` with the new edge `other`, returning the old connection
    ///
    /// # Panics
    /// Panics if `self` was not correctly initialized or was mangled, resulting in a `None` connection.
    pub fn set_connection(
        &mut self,
        other: Rc<RefCell<TnurccEdge<P>>>,
        con: TnurccConnection,
    ) -> Rc<RefCell<TnurccEdge<P>>> {
        return self.connections[con as usize]
            .replace(other)
            .expect("TnurccEdge should always have a Some(connection)");
    }

    /// Returns the next anti-clockwise edge around `self`'s vertex `p`.
    ///
    /// # Returns
    /// - `None` if `p` is not an end of `self`.
    ///
    /// - `Some(edge)` otherwise.
    pub fn acw_edge_from_point(
        &self,
        p: Rc<RefCell<TnurccControlPoint<P>>>,
    ) -> Option<Rc<RefCell<TnurccEdge<P>>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match self.point_end(p)? {
            TnurccVertexEnd::Origin => TnurccConnection::LeftCw,
            TnurccVertexEnd::Dest => TnurccConnection::RightCw,
        };

        Some(self.connection(dir))
    }

    /// Returns the next clockwise edge around `self`'s vertex `p`.
    ///
    /// # Returns
    /// - `None` if `p` is not an end of `self`.
    ///
    /// - `Some(edge)` otherwise.
    pub fn cw_edge_from_point(
        &self,
        p: Rc<RefCell<TnurccControlPoint<P>>>,
    ) -> Option<Rc<RefCell<TnurccEdge<P>>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match self.point_end(p)? {
            TnurccVertexEnd::Origin => TnurccConnection::RightAcw,
            TnurccVertexEnd::Dest => TnurccConnection::LeftAcw,
        };

        Some(self.connection(dir))
    }

    /// Returns the `n`th anti-clockwise edge around `e`'s vertex `p`.
    ///
    /// # Returns
    /// - `None` if `p` is not a point connected to either end of any edge between and including `e` and
    ///     the destination edge.
    ///
    /// - `Some(edge)` otherwise.
    ///
    /// # Borrows
    /// Immutably borrows every edge connected to `p` between and including `e` and the destination edge.
    pub fn nth_acw_edge_from_point(
        e: Rc<RefCell<TnurccEdge<P>>>,
        p: Rc<RefCell<TnurccControlPoint<P>>>,
        n: usize,
    ) -> Option<Rc<RefCell<TnurccEdge<P>>>> {
        let mut e = e;
        for _ in 0..n {
            e = {
                let borrow = e.borrow();
                borrow.acw_edge_from_point(Rc::clone(&p))?
            };
        }
        return Some(e);
    }

    /// Returns the `n`th clockwise edge around `e`'s vertex `p`.
    ///
    /// # Returns
    /// - `None` if `p` is not a point connected to either end of any edge between and including `e` and
    ///     the destination edge.
    ///
    /// - `Some(edge)` otherwise.
    ///
    /// # Borrows
    /// Immutably borrows every edge connected to `p` between and including `e` and the destination edge.
    pub fn nth_cw_edge_from_point(
        e: Rc<RefCell<TnurccEdge<P>>>,
        p: Rc<RefCell<TnurccControlPoint<P>>>,
        n: usize,
    ) -> Option<Rc<RefCell<TnurccEdge<P>>>> {
        let mut e = e;
        for _ in 0..n {
            e = {
                let borrow = e.borrow();
                borrow.cw_edge_from_point(Rc::clone(&p))?
            };
        }
        return Some(e);
    }

    /// Returns the next anti-clockwise edge around `self`'s vertex `end`.
    pub fn acw_edge_from_end(&self, end: TnurccVertexEnd) -> Rc<RefCell<TnurccEdge<P>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match end {
            TnurccVertexEnd::Origin => TnurccConnection::LeftCw,
            TnurccVertexEnd::Dest => TnurccConnection::RightCw,
        };

        self.connection(dir)
    }

    /// Returns the next clockwise edge around `self`'s vertex `end`.
    #[allow(dead_code)]
    pub fn cw_edge_from_end(&self, end: TnurccVertexEnd) -> Rc<RefCell<TnurccEdge<P>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match end {
            TnurccVertexEnd::Origin => TnurccConnection::RightAcw,
            TnurccVertexEnd::Dest => TnurccConnection::LeftAcw,
        };

        self.connection(dir)
    }

    /// Returns the next anti-clockwise edge around `self`'s face `f`.
    ///
    /// # Returns
    /// - `None` if `f` is not on either side of `self`.
    ///
    /// - `Some(edge)` otherwise.
    #[allow(dead_code)]
    pub fn acw_edge_from_face(
        &self,
        f: Rc<RefCell<TnurccFace<P>>>,
    ) -> Option<Rc<RefCell<TnurccEdge<P>>>> {
        // Determine which side the face is connected to.
        let dir = match self.face_side(f)? {
            TnurccFaceSide::Left => TnurccConnection::LeftAcw,
            TnurccFaceSide::Right => TnurccConnection::RightAcw,
        };

        Some(self.connection(dir))
    }

    /// Returns the next clockwise edge around `self`'s face `f`.
    ///
    /// # Returns
    /// - `None` if `f` is not on either side of `self`.
    ///
    /// - `Some(edge)` otherwise.
    #[allow(dead_code)]
    pub fn cw_edge_from_face(
        &self,
        f: Rc<RefCell<TnurccFace<P>>>,
    ) -> Option<Rc<RefCell<TnurccEdge<P>>>> {
        // Determine which side the face is connected to.
        let dir = match self.face_side(f)? {
            TnurccFaceSide::Left => TnurccConnection::LeftCw,
            TnurccFaceSide::Right => TnurccConnection::RightCw,
        };

        Some(self.connection(dir))
    }

    /// Returns the next anti-clockwise edge around `self`'s face `side`.
    pub fn acw_edge_from_side(&self, side: TnurccFaceSide) -> Rc<RefCell<TnurccEdge<P>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match side {
            TnurccFaceSide::Left => TnurccConnection::LeftAcw,
            TnurccFaceSide::Right => TnurccConnection::RightAcw,
        };

        self.connection(dir)
    }

    /// Returns the next clockwise edge around `self`'s face `side`.
    #[allow(dead_code)]
    pub fn cw_edge_from_side(&self, side: TnurccFaceSide) -> Rc<RefCell<TnurccEdge<P>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match side {
            TnurccFaceSide::Left => TnurccConnection::LeftCw,
            TnurccFaceSide::Right => TnurccConnection::RightCw,
        };

        self.connection(dir)
    }

    /// Returns the end that `point` is located on, if any.
    ///
    /// # Returns
    /// - `Some(end)` if `point` is connected to `self`.
    ///
    /// - `None` otherwise.
    pub fn point_end(&self, point: Rc<RefCell<TnurccControlPoint<P>>>) -> Option<TnurccVertexEnd> {
        if std::ptr::eq(self.origin.as_ref(), point.as_ref()) {
            Some(TnurccVertexEnd::Origin)
        } else if std::ptr::eq(self.dest.as_ref(), point.as_ref()) {
            Some(TnurccVertexEnd::Dest)
        } else {
            None
        }
    }

    /// Returns the point on the end `end`.
    pub fn point_at_end(&self, end: TnurccVertexEnd) -> Rc<RefCell<TnurccControlPoint<P>>> {
        use TnurccVertexEnd::*;
        match end {
            Origin => Rc::clone(&self.origin),
            Dest => Rc::clone(&self.dest),
        }
    }

    /// Returns which side the face `face` is on, if it is on any. Note that the side is always relative to the "vector"
    /// of the edge pointing "up", that is, the source point is the first anti-clockwise point out of the origin dest
    /// pair to be encountered on the left face, and the last anti-clockwise point out of the pair to be encountered on
    /// the right.
    ///
    /// # Returns
    /// - `Some(side)` if `face` is connected to `self`.
    ///
    /// - `None` if `self` is not connected to `face`.
    pub fn face_side(&self, face: Rc<RefCell<TnurccFace<P>>>) -> Option<TnurccFaceSide> {
        if self
            .face_left
            .as_ref()
            .is_some_and(|f| std::ptr::eq(Rc::as_ref(f), face.as_ref()))
        {
            Some(TnurccFaceSide::Left)
        } else if self
            .face_right
            .as_ref()
            .is_some_and(|f| std::ptr::eq(Rc::as_ref(f), face.as_ref()))
        {
            Some(TnurccFaceSide::Right)
        } else {
            None
        }
    }

    /// Returns the face on the side `side`, if it exists.
    ///
    /// # Returns
    /// - `Some(face)` if the face on `side` exists.
    ///
    /// - `None` if the face on `side` does not exist.
    pub fn face_from_side(&self, side: TnurccFaceSide) -> Option<Rc<RefCell<TnurccFace<P>>>> {
        use TnurccFaceSide::*;
        match side {
            Left => self.face_left.as_ref().map(|f| Rc::clone(f)),
            Right => self.face_right.as_ref().map(|f| Rc::clone(f)),
        }
    }

    /// Get the orientations in `self.connections` which correspond to the connections with the edge `other`.
    ///
    /// # Panics
    /// Panics if `self` has been incorrectly configured with `None` connections.
    #[allow(dead_code)]
    pub fn connection_orientation(
        &self,
        other: Rc<RefCell<TnurccEdge<P>>>,
    ) -> Vec<TnurccConnection> {
        self.connections
            .iter()
            .enumerate()
            .filter(|(_, r)| {
                std::ptr::eq(
                r
                .as_ref()
                .expect("Edges should have Some(connection) in connections in all circumstances")
                .as_ref(),
                other.as_ref()
            )
            })
            .map(|(i, _)| TnurccConnection::from_usize(i))
            .collect()
    }

    /// Splits an edge into two, placing a new control point at `p` with index `point_index` between them.
    /// The edge `e` will remain as the edge connecting `e`'s `origin` to the new control point, and a new
    /// conjugate edge will be created between the new control point and `e`'s old `dest`. The index of the new
    /// edge will be `edge_index`. Both faces are copied from `e` to the new edge and connections from the
    /// `dest` end of `e` are connected to the conjugate edge using the `connect` function. All edges
    /// connected to `e.dest` are reconnected to the new edge.
    ///
    /// # Ratio
    /// `ratio` describes the relationship between the knot ratios of the two new edge and `e` prior to calling
    /// `split_edge`. Specifically, the knot interval of the new edge will be `e.knot_interval * (1.0 - ratio)` and
    /// the knot interval of `e` after calling `split_edge` will be `e.knot_interval * ratio`.
    ///
    /// # Returns
    /// - `TnurccMalformedFace` if the connections from the original edge cannot be transfered to the split
    ///     edge conjugate.
    ///
    /// - `Ok(TnurccControlPoint)` if the edge is successfully split.
    ///
    /// # Borrows
    /// Mutably borros `e`
    pub fn split_edge(
        e: Rc<RefCell<TnurccEdge<P>>>,
        edge_index: usize,
        p: P,
        point_index: usize,
        ratio: f64,
    ) -> Result<Rc<RefCell<TnurccControlPoint<P>>>> {
        let point = Rc::new(RefCell::new(TnurccControlPoint::new(point_index, p)));
        let conjugate = TnurccEdge::new(
            edge_index,
            (1.0 - ratio) * e.borrow().knot_interval,
            Rc::clone(&point),
            Rc::clone(&e.borrow().dest),
        );

        conjugate.borrow_mut().face_right = e.borrow().face_right.as_ref().map(|r| Rc::clone(r));
        conjugate.borrow_mut().face_left = e.borrow().face_left.as_ref().map(|r| Rc::clone(r));

        e.borrow_mut().dest = Rc::clone(&point);
        e.borrow_mut().knot_interval *= ratio;

        point.borrow_mut().valence = 2;
        point.borrow_mut().incoming_edge = Some(Rc::clone(&e));

        conjugate.borrow().dest.borrow_mut().incoming_edge = Some(Rc::clone(&conjugate));

        for con in [TnurccConnection::LeftAcw, TnurccConnection::RightCw] {
            let other = e.borrow().connection(con);
            TnurccEdge::connect(Rc::clone(&other), Rc::clone(&conjugate))
                .map_err(|_| Error::TnurccMalformedFace)?;
        }

        TnurccEdge::connect(Rc::clone(&e), Rc::clone(&conjugate))
            .map_err(|_| Error::TnurccMalformedFace)?;

        Ok(point)
    }

    /// Returns the face shared between two edges.
    ///
    /// # Returns
    /// - `None` if no such face exists.
    ///
    /// - `Some(face)` if such a face exists.
    ///  
    /// # Borrows
    /// Immutably borrows `other`.
    ///
    /// # Panics
    /// Panics if any borrow fails.
    pub fn common_face(&self, other: Rc<RefCell<Self>>) -> Option<Rc<RefCell<TnurccFace<P>>>> {
        let other = other.borrow();

        if let Some(ref first_left_face) = self.face_left {
            if other
                .face_left
                .as_ref()
                .is_some_and(|r| std::ptr::eq(r.as_ref(), first_left_face.as_ref()))
            {
                return Some(Rc::clone(&first_left_face));
            };

            if other
                .face_right
                .as_ref()
                .is_some_and(|r| std::ptr::eq(r.as_ref(), first_left_face.as_ref()))
            {
                return Some(Rc::clone(&first_left_face));
            }
        }

        if let Some(ref first_right_face) = self.face_right {
            if other
                .face_left
                .as_ref()
                .is_some_and(|r| std::ptr::eq(r.as_ref(), first_right_face.as_ref()))
            {
                return Some(Rc::clone(&first_right_face));
            }

            if other
                .face_right
                .as_ref()
                .is_some_and(|r| std::ptr::eq(r.as_ref(), first_right_face.as_ref()))
            {
                return Some(Rc::clone(&first_right_face));
            }
        }

        None
    }

    /// Returns the point shared between two edges.
    ///
    /// # Returns
    /// - `None` if no such points exists.
    ///
    /// - `Some(point)` if such a point exists.
    ///  
    /// # Borrows
    /// Immutably borrows `other`.
    ///
    /// # Panics
    /// Panics if any borrow fails.
    #[allow(dead_code)]
    pub fn common_point(
        &self,
        other: Rc<RefCell<Self>>,
    ) -> Option<Rc<RefCell<TnurccControlPoint<P>>>> {
        let other = other.borrow();

        if std::ptr::eq(self.origin.as_ref(), other.origin.as_ref())
            || std::ptr::eq(self.origin.as_ref(), other.dest.as_ref())
        {
            Some(Rc::clone(&self.origin))
        } else if std::ptr::eq(self.dest.as_ref(), other.origin.as_ref())
            || std::ptr::eq(self.dest.as_ref(), other.dest.as_ref())
        {
            Some(Rc::clone(&self.dest))
        } else {
            None
        }
    }

    /// Automatically tries to connect two edges `first` and `other` that share at least one vertex and one face.
    /// Performs this agnostic of the current connections of both edges, and does not modify any connections it does
    /// not have to. Note that the algorithm greedily connects the edges for up to two of four possible connections.
    ///
    /// # Returns
    /// - `TnurccBadConnectionConditions` if the two edges were not able to be connected.
    ///
    /// - `Ok()` otherwise.
    ///
    /// # Borrows
    /// Mutably borrows `first` and `other`.
    ///
    /// # Panics
    /// Panics if any borrows fail.
    ///
    /// # Undefined Behaviour
    /// Undefined if `first` and `other` are the same edge instance, or if all the relevant members are identical between the two.
    pub fn connect(
        first: Rc<RefCell<TnurccEdge<P>>>,
        other: Rc<RefCell<TnurccEdge<P>>>,
    ) -> Result<()> {
        use TnurccConnection::*;

        let mut face_config = Vec::with_capacity(4);
        let mut vert_config = Vec::with_capacity(4);

        let first_left = first.borrow().face_left.as_ref().map(|r| Rc::clone(r));
        let first_right = first.borrow().face_right.as_ref().map(|r| Rc::clone(r));
        let other_left = other.borrow().face_left.as_ref().map(|r| Rc::clone(r));
        let other_right = other.borrow().face_right.as_ref().map(|r| Rc::clone(r));

        let first_orig = Rc::clone(&first.borrow().origin);
        let first_dest = Rc::clone(&first.borrow().dest);
        let other_orig = Rc::clone(&other.borrow().origin);
        let other_dest = Rc::clone(&other.borrow().dest);

        // Which faces are equal to each other (None != None in this case)
        // 0 -> first.left  == other.left
        // 1 -> first.right == other.right
        // 2 -> first.left  == other.right
        // 3 -> first.right == other.left
        if let Some(first_left_face) = first_left {
            if other_left
                .as_ref()
                .is_some_and(|r| std::ptr::eq(r.as_ref(), first_left_face.as_ref()))
            {
                face_config.push(0);
            };

            if other_right
                .as_ref()
                .is_some_and(|r| std::ptr::eq(r.as_ref(), first_left_face.as_ref()))
            {
                face_config.push(2);
            }
        }

        if let Some(first_right_face) = first_right {
            if other_left.is_some_and(|r| std::ptr::eq(r.as_ref(), first_right_face.as_ref())) {
                face_config.push(3);
            }

            if other_right.is_some_and(|r| std::ptr::eq(r.as_ref(), first_right_face.as_ref())) {
                face_config.push(1);
            }
        }

        // 0 -> first.origin == other.dest
        // 1 -> first.dest   == other.origin
        // 2 -> first.origin == other.origin
        // 3 -> first.dest   == other.dest
        if std::ptr::eq(first_orig.as_ref(), other_dest.as_ref()) {
            vert_config.push(0);
        } else if std::ptr::eq(first_dest.as_ref(), other_orig.as_ref()) {
            vert_config.push(1);
        } else if std::ptr::eq(first_orig.as_ref(), other_orig.as_ref()) {
            vert_config.push(2);
        } else if std::ptr::eq(first_dest.as_ref(), other_dest.as_ref()) {
            vert_config.push(3);
        }

        // Face states:
        // 0 -> self.left  == other.left
        // 1 -> self.right == other.right
        // 2 -> self.left  == other.right
        // 3 -> self.right == other.left
        //
        // Vert states:
        // 0 -> self.origin == other.dest
        // 1 -> self.dest   == other.origin
        // 2 -> self.origin == other.origin
        // 3 -> self.dest   == other.dest
        //
        // Vert states and Face states are grouped together such that "valid" states (states which will result in
        // a new connection being created) are combinations of lower or upper half face and vertex states. That is,
        // for a state (face, vert), valid states are any combination of 1 and 0, or of 2 and 3; (0, 1), (2, 3), (3, 2), etc...
        // Invalid states are any combination of (0 or 1) and (2 or 3); (1, 3), (0, 2), (3, 0), etc...
        let mut valid_state_reached = false;
        let directions = vec![LeftCw, LeftAcw, RightCw, RightAcw];
        for face_state in face_config {
            for vert_state in vert_config.iter().cloned() {
                // Vertex and face state to self and other direction indicies
                // (f, v) | (s, o) | ab cd | ef gh |
                // -------+--------+-------+-------|
                // (0, 0) | (0, 1) | 00 00 | 00 01 |
                // (0, 1) | (1, 0) | 00 01 | 01 00 |
                // (1, 0) | (3, 2) | 01 00 | 11 10 |
                // (1, 1) | (2, 3) | 01 01 | 10 11 |
                // (2, 2) | (0, 3) | 10 10 | 00 11 |
                // (2, 3) | (1, 2) | 10 11 | 01 10 |
                // (3, 2) | (3, 0) | 11 10 | 11 00 |
                // (3, 3) | (2, 1) | 11 11 | 10 01 |
                //
                // Through https://ictlab.kz/extra/Kmap/:
                // e(a, b, c, d) = b
                // f(a, b, c, d) = bd' + b'd => b ^ d
                // g(a, b, c, d) = a'b + ab' => a ^ b
                // h(a, b, c, d) = bd + b'd' => b ^ 'd
                valid_state_reached = true;
                let a = face_state > 1;
                let b = face_state % 2 == 1;
                let c = vert_state > 1;
                let d = vert_state % 2 == 1;
                let d_prime = !d;

                // Bad state, ignore and continue
                // a'c + ac' => a ^ c
                if a ^ c {
                    continue;
                }

                // e(a, b, c, d) = b
                let e = b;
                // f(a, b, c, d) = b ^ d
                let f = b ^ d;
                // g(a, b, c, d) = a ^ b
                let g = a ^ b;
                // h(a, b, c, d) = b ^ 'd
                let h = b ^ d_prime;

                let self_index = if e { 2 } else { 0 } + if f { 1 } else { 0 };
                let other_index = if g { 2 } else { 0 } + if h { 1 } else { 0 };

                let sub_directions = [directions[self_index], directions[other_index]];

                first
                    .borrow_mut()
                    .set_connection(Rc::clone(&other), sub_directions[0]);
                other
                    .borrow_mut()
                    .set_connection(Rc::clone(&first), sub_directions[1]);
            }
        }

        if valid_state_reached {
            Ok(())
        } else {
            Err(Error::TnurccBadConnectionConditions(
                first.borrow().index,
                other.borrow().index,
            ))
        }
    }
}

impl<P> Drop for TnurccEdge<P> {
    fn drop(&mut self) {
        for i in 0..self.connections.len() {
            self.connections[i] = None;
        }

        self.face_left = None;
        self.face_right = None;
    }
}

impl<P> fmt::Display for TnurccEdge<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Index: {}\n\tOrigin: {}\n\tDest: {}\n\tFace Left: {}\n\tFace Right: {}\n{}-----{}\n   |\n{}-----{}", 
            self.index,
            self.origin.borrow().index,
            self.dest.borrow().index,
            self.face_left.as_ref().map_or(-1, |f| f.borrow().index as i32),
            self.face_right.as_ref().map_or(-1, |f| f.borrow().index as i32),
            self.connections[TnurccConnection::LeftAcw as usize].as_ref().map_or(-1, |e| e.borrow().index as i32),
            self.connections[TnurccConnection::RightCw as usize].as_ref().map_or(-1, |e| e.borrow().index as i32),
            self.connections[TnurccConnection::LeftCw as usize].as_ref().map_or(-1, |e| e.borrow().index as i32),
            self.connections[TnurccConnection::RightAcw as usize].as_ref().map_or(-1, |e| e.borrow().index as i32),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests if `connect` will properly connect two edges which share only one face.
    #[test]
    fn test_tnurcc_edge_connect_single_shared_face() {
        use TnurccConnection::*;
        use TnurccFaceSide::*;
        // Primary control points
        let primary_origin = Rc::new(RefCell::new(TnurccControlPoint::new(0, (0.0, 0.0, 0.0))));
        let prmiary_dest = Rc::new(RefCell::new(TnurccControlPoint::new(1, (0.0, 1.0, 0.0))));

        // Primary edge
        let primary_edge =
            TnurccEdge::new(0, 1.0, Rc::clone(&primary_origin), Rc::clone(&prmiary_dest));

        // Faces for orientation
        let left_face = Rc::new(RefCell::new(TnurccFace {
            index: 0,
            edge: Some(Rc::clone(&primary_edge)),
            corners: [const { None }; 4],
        }));
        let right_face = Rc::new(RefCell::new(TnurccFace {
            index: 1,
            edge: Some(Rc::clone(&primary_edge)),
            corners: [const { None }; 4],
        }));

        // Connection of faces
        primary_edge.borrow_mut().face_left = Some(Rc::clone(&left_face));
        primary_edge.borrow_mut().face_right = Some(Rc::clone(&right_face));

        // The four points which the secondary may connect to. Each on is located in a corner, bl = bottom left and so on.
        // The secondary vector will connect to one of these and one of the primary control points
        let secondary_bl = Rc::new(RefCell::new(TnurccControlPoint::new(2, (-1.0, 0.0, 0.0))));
        let secondary_br = Rc::new(RefCell::new(TnurccControlPoint::new(3, (1.0, 0.0, 0.0))));
        let secondary_tr = Rc::new(RefCell::new(TnurccControlPoint::new(4, (1.0, 1.0, 0.0))));
        let secondary_tl = Rc::new(RefCell::new(TnurccControlPoint::new(5, (-1.0, 1.0, 0.0))));

        // All possible valid configurations
        let test_parameters = vec![
            (
                Rc::clone(&secondary_bl),   // Secondary origin
                Rc::clone(&primary_origin), // Secondary dest
                Left,                       // Common face
                Left,                       // Secondary edge common face side
                LeftCw,                     // Primary edge connection side
                LeftAcw,                    // Secondary edge connectioin side
            ),
            (
                Rc::clone(&prmiary_dest),
                Rc::clone(&secondary_tl),
                Left,
                Left,
                LeftAcw,
                LeftCw,
            ),
            (
                Rc::clone(&secondary_br),
                Rc::clone(&primary_origin),
                Right,
                Right,
                RightAcw,
                RightCw,
            ),
            (
                Rc::clone(&prmiary_dest),
                Rc::clone(&secondary_tr),
                Right,
                Right,
                RightCw,
                RightAcw,
            ),
            (
                Rc::clone(&primary_origin),
                Rc::clone(&secondary_bl),
                Left,
                Right,
                LeftCw,
                RightAcw,
            ),
            (
                Rc::clone(&secondary_tl),
                Rc::clone(&prmiary_dest),
                Left,
                Right,
                LeftAcw,
                RightCw,
            ),
            (
                Rc::clone(&primary_origin),
                Rc::clone(&secondary_br),
                Right,
                Left,
                RightAcw,
                LeftCw,
            ),
            (
                Rc::clone(&secondary_tr),
                Rc::clone(&prmiary_dest),
                Right,
                Left,
                RightCw,
                LeftAcw,
            ),
        ];

        for (org, dst, cmn_f, cmn_f_side, p_con_side, s_con_side) in test_parameters {
            let secondary_edge = TnurccEdge::new(1, 1.0, Rc::clone(&org), Rc::clone(&dst));
            let common_face = Rc::clone(if cmn_f == Left {
                &left_face
            } else {
                &right_face
            });
            match cmn_f_side {
                Left => secondary_edge.borrow_mut().face_left = Some(common_face),
                Right => secondary_edge.borrow_mut().face_right = Some(common_face),
            };

            let con_res = TnurccEdge::connect(Rc::clone(&primary_edge), Rc::clone(&secondary_edge));
            assert!(
                con_res.is_ok(),
                "Connection between {:?}->{:?} and {:?}->{:?} failed with error: {}.",
                primary_edge.borrow().origin.borrow().point,
                primary_edge.borrow().dest.borrow().point,
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point,
                con_res.err().unwrap()
            );

            // Check if the primary edge is connected to the secondary
            let primary_con_orientaion = primary_edge
                .borrow()
                .connection_orientation(Rc::clone(&secondary_edge));
            assert_eq!(
                primary_con_orientaion.len(),
                1,
                "Primary edge is not connected to secondary the correct number of times \
                for secondary {:?}->{:?}.",
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point
            );
            let primary_con_orientaion = primary_con_orientaion[0];

            // Check if the connection orientation is correct
            assert_eq!(
                p_con_side,
                primary_con_orientaion,
                "Primary edge is not correctly connected to secondary edge for \
                secondary edge {:?}->{:?}.",
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point
            );

            // Check if the secondary edge is connected to the primary
            let secondary_con_orientaion = secondary_edge
                .borrow()
                .connection_orientation(Rc::clone(&primary_edge));
            assert_eq!(
                secondary_con_orientaion.len(),
                1,
                "Secondary edge is not connected to primary the correct number of times \
                for secondary {:?}->{:?}.",
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point
            );
            let secondary_con_orientaion = secondary_con_orientaion[0];

            // Check if the connection orientation is correct
            assert_eq!(
                s_con_side,
                secondary_con_orientaion,
                "Secondary edge is not correctly connected to primary edge for \
                secondary edge {:?}->{:?}.",
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point
            );

            // Reset the primary edge.
            primary_edge
                .borrow_mut()
                .set_connection(Rc::clone(&primary_edge), p_con_side);
        }
    }

    /// Tests if `connect` will properly connect two edges which are "inline" with each other, that is, they share two faces.
    #[test]
    fn test_tnurcc_edge_connect_double_shared_face() {
        use TnurccConnection::*;
        use TnurccFaceSide::*;
        // Primary control points
        let primary_origin = Rc::new(RefCell::new(TnurccControlPoint::new(0, (0.0, 0.0, 0.0))));
        let prmiary_dest = Rc::new(RefCell::new(TnurccControlPoint::new(1, (0.0, 1.0, 0.0))));

        // The primary edge
        let primary_edge =
            TnurccEdge::new(0, 1.0, Rc::clone(&primary_origin), Rc::clone(&prmiary_dest));

        // Faces
        let left_face = Rc::new(RefCell::new(TnurccFace {
            index: 0,
            edge: Some(Rc::clone(&primary_edge)),
            corners: [const { None }; 4],
        }));
        let right_face = Rc::new(RefCell::new(TnurccFace {
            index: 1,
            edge: Some(Rc::clone(&primary_edge)),
            corners: [const { None }; 4],
        }));

        // Set the faces of the primary
        primary_edge.borrow_mut().face_left = Some(Rc::clone(&left_face));
        primary_edge.borrow_mut().face_right = Some(Rc::clone(&right_face));

        // Two points which are on either side of the primary
        let secondary_top = Rc::new(RefCell::new(TnurccControlPoint::new(2, (0.0, 2.0, 0.0))));
        let secondary_bottom = Rc::new(RefCell::new(TnurccControlPoint::new(3, (0.0, -1.0, 0.0))));

        // The various possible valid configurations for connecting the two points in this way.
        let test_parameters = vec![
            (
                Rc::clone(&secondary_top), // Secondary origin
                Rc::clone(&prmiary_dest),  // Secondary dest
                Right,                     // left_face side
                [LeftAcw, RightCw],        // Secondary to primary connections
                [LeftAcw, RightCw],        // Primary to secondary connections
            ),
            (
                Rc::clone(&prmiary_dest),
                Rc::clone(&secondary_top),
                Left,
                [LeftCw, RightAcw],
                [LeftAcw, RightCw],
            ),
            (
                Rc::clone(&secondary_bottom),
                Rc::clone(&primary_origin),
                Left,
                [LeftAcw, RightCw],
                [LeftCw, RightAcw],
            ),
            (
                Rc::clone(&primary_origin),
                Rc::clone(&secondary_bottom),
                Right,
                [LeftCw, RightAcw],
                [LeftCw, RightAcw],
            ),
        ];

        for (s_org, s_dest, left_face_side, s_con_sides, p_con_sides) in test_parameters {
            // Construct the secondary edge according to the provided parameters
            let secondary_edge = TnurccEdge::new(1, 1.0, Rc::clone(&s_org), Rc::clone(&s_dest));

            // Face orientation varries
            if left_face_side == Left {
                secondary_edge.borrow_mut().face_left = Some(Rc::clone(&left_face));
                secondary_edge.borrow_mut().face_right = Some(Rc::clone(&right_face));
            } else {
                secondary_edge.borrow_mut().face_left = Some(Rc::clone(&right_face));
                secondary_edge.borrow_mut().face_right = Some(Rc::clone(&left_face));
            }

            // Attempt to connect
            let con_res = TnurccEdge::connect(Rc::clone(&primary_edge), Rc::clone(&secondary_edge));
            assert!(
                con_res.is_ok(),
                "Connection between {:?}->{:?} and {:?}->{:?} failed with error: {}.",
                primary_edge.borrow().origin.borrow().point,
                primary_edge.borrow().dest.borrow().point,
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point,
                con_res.err().unwrap()
            );

            // Check if the primary edge is connected to the secondary
            let primary_con_orientaion = primary_edge
                .borrow()
                .connection_orientation(Rc::clone(&secondary_edge));
            assert_eq!(
                primary_con_orientaion.len(),
                2,
                "Primary edge is not connected to secondary the correct number of times \
                for secondary {:?}->{:?}.",
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point
            );

            // Check if the connection orientation is correct
            for expect in p_con_sides.iter() {
                assert!(
                    primary_con_orientaion.contains(expect),
                    "Primary edge is not correctly connected to secondary edge for \
                    secondary edge {:?}->{:?}'s connection {}.",
                    secondary_edge.borrow().origin.borrow().point,
                    secondary_edge.borrow().dest.borrow().point,
                    *expect
                );
            }

            // Check if the secondary edge is connected to the primary
            let secondary_con_orientaion = secondary_edge
                .borrow()
                .connection_orientation(Rc::clone(&primary_edge));
            assert_eq!(
                secondary_con_orientaion.len(),
                2,
                "Secondary edge is not connected to primary the correct number of times \
                for secondary {:?}->{:?}.",
                secondary_edge.borrow().origin.borrow().point,
                secondary_edge.borrow().dest.borrow().point
            );

            // Check if the connection orientation is correct
            for expect in s_con_sides.iter() {
                assert!(
                    secondary_con_orientaion.contains(expect),
                    "Secondary edge is not correctly connected to primary edge for \
                    secondary edge {:?}->{:?}'s connection {}.",
                    secondary_edge.borrow().origin.borrow().point,
                    secondary_edge.borrow().dest.borrow().point,
                    *expect
                );
            }

            // Reset the primary edge.
            for i in 0..4 {
                primary_edge
                    .borrow_mut()
                    .set_connection(Rc::clone(&primary_edge), TnurccConnection::from_usize(i));
            }
        }
    }

    /// Tests `split_edge`, checking to make sure that the logic for splitting the edge into two,
    /// with a control point between them, is functioning as expected
    #[test]
    fn test_tnurcc_split_edge() {
        // Control points needed
        let origin = Rc::new(RefCell::new(TnurccControlPoint::new(
            0,
            Point3::from((0.0, 0.0, 0.0)),
        )));
        let dest = Rc::new(RefCell::new(TnurccControlPoint::new(
            1,
            Point3::from((0.0, 5.0, 0.0)),
        )));

        // Edge to be split
        let edge = TnurccEdge::new(0, 2.5, Rc::clone(&origin), Rc::clone(&dest));

        // Faces for connections
        let left_face = Rc::new(RefCell::new(TnurccFace {
            index: 0,
            edge: Some(Rc::clone(&edge)),
            corners: [const { None }; 4],
        }));
        let right_face = Rc::new(RefCell::new(TnurccFace {
            index: 0,
            edge: Some(Rc::clone(&edge)),
            corners: [const { None }; 4],
        }));

        edge.borrow_mut().face_left = Some(Rc::clone(&left_face));
        edge.borrow_mut().face_right = Some(Rc::clone(&right_face));

        // Set the incoming edge to an edge it wont be connected to after edge splitting, to test if it gets reasigned correctly
        dest.borrow_mut().incoming_edge = Some(Rc::clone(&edge));

        // Split the edge
        let middle = TnurccEdge::split_edge(
            Rc::clone(&edge),
            24,
            Point3::from((0.0, 1.0, 0.0)),
            56,
            0.25,
        )
        .expect("Splitting is designed to succeed");

        // Get the new edge, other_left and other_right should be the same
        let other_left = edge.borrow().connection(TnurccConnection::LeftAcw);
        let other_right = edge.borrow().connection(TnurccConnection::RightCw);

        // Check that edge is correctly connected to an edge
        assert!(
            std::ptr::eq(other_left.as_ref(), other_right.as_ref()),
            "New edge was not properly connected."
        );
        // Check that the above edge is a new edge
        assert!(
            !std::ptr::eq(other_left.as_ref(), edge.as_ref()),
            "New edge was not properly created or connected."
        );
        // Check that the old edge was correctly modified
        assert!(
            std::ptr::eq(edge.borrow().dest.as_ref(), middle.as_ref()),
            "Edge's destination is incorrect."
        );
        // Check that the new edge has the correct desitination
        assert!(
            std::ptr::eq(other_left.borrow().dest.as_ref(), dest.as_ref()),
            "New edge's destination is incorrect."
        );
        // Check that edge's knot interval is correct
        assert!(
            (edge.borrow().knot_interval - 0.625).so_small(),
            "Edge's knot interval is incorrect."
        );
        // Check that the new edge's knot interval is correct
        assert!(
            (other_left.borrow().knot_interval - 1.875).so_small(),
            "New edge's knot interval is incorrect."
        );
        // Check the valence of the new point
        assert_eq!(middle.borrow().valence, 2, "Point valence is incorrect.");
        // Check the index of the new point
        assert_eq!(middle.borrow().index, 56, "Point index is incorrect.");
        // Check that the new point's incomming edge is an edge that is
        // connected to the new point
        assert!(
            middle
                .borrow()
                .incoming_edge
                .as_ref()
                .unwrap()
                .borrow()
                .point_end(Rc::clone(&middle))
                .is_some(),
            "Middle's incomming edge is incorrect."
        );
        // Check that the new edge's index is correct
        assert_eq!(
            other_left.borrow().index,
            24,
            "New edge index is incorrect."
        );

        // Check that the destination point's incoming edge has been correctly set
        assert!(
            std::ptr::eq(
                other_left.as_ref(),
                dest.borrow()
                    .incoming_edge
                    .as_ref()
                    .expect("Incoming edge for dest should have been set")
                    .as_ref()
            ),
            "Incomming edge for destination was not correctly set to new edge."
        );
    }

    /// Tests if splitting an edge which is connected to other edges correctly mutates the edges it is connected to,
    /// so that they no longer refer to an edge they aren't topologically connected to.
    #[test]
    fn test_tnurcc_split_edge_connected_edges() {
        // Control points to be used in the test. tl and tr are top left and top right respectively
        let origin = Rc::new(RefCell::new(TnurccControlPoint::new(
            0,
            Point3::from((0.0, 0.0, 0.0)),
        )));
        let dest = Rc::new(RefCell::new(TnurccControlPoint::new(
            1,
            Point3::from((0.0, 5.0, 0.0)),
        )));
        let tl = Rc::new(RefCell::new(TnurccControlPoint::new(
            1,
            Point3::from((-1.0, 5.0, 0.0)),
        )));
        let tr = Rc::new(RefCell::new(TnurccControlPoint::new(
            1,
            Point3::from((1.0, 5.0, 0.0)),
        )));

        // Edges to be used. left_edge and right_edge are the edges which will not be split,
        // but must be reconnected to the new edge.
        let left_edge = TnurccEdge::new(0, 2.5, Rc::clone(&tl), Rc::clone(&dest));
        let right_edge = TnurccEdge::new(1, 2.5, Rc::clone(&tr), Rc::clone(&dest));
        let edge = TnurccEdge::new(2, 2.5, Rc::clone(&origin), Rc::clone(&dest));

        // Faces, needed for connecting and reconnecting
        let left_face = Rc::new(RefCell::new(TnurccFace {
            index: 0,
            edge: Some(Rc::clone(&edge)),
            corners: [const { None }; 4],
        }));
        let right_face = Rc::new(RefCell::new(TnurccFace {
            index: 0,
            edge: Some(Rc::clone(&edge)),
            corners: [const { None }; 4],
        }));

        // Set the faces of the edges and connect them together
        edge.borrow_mut().face_left = Some(Rc::clone(&left_face));
        edge.borrow_mut().face_right = Some(Rc::clone(&right_face));

        left_edge.borrow_mut().face_right = Some(Rc::clone(&left_face));
        right_edge.borrow_mut().face_left = Some(Rc::clone(&right_face));

        TnurccEdge::connect(Rc::clone(&edge), Rc::clone(&right_edge))
            .expect("Connection should be topologically consistent");
        TnurccEdge::connect(Rc::clone(&edge), Rc::clone(&left_edge))
            .expect("Connection should be topologically consistent");

        // Split the edge (parameters are the same from the previous test, but will not be checked)
        let _middle = TnurccEdge::split_edge(
            Rc::clone(&edge),
            24,
            Point3::from((0.0, 1.0, 0.0)),
            56,
            0.25,
        );

        // Get the new edge
        let new_edge = edge.borrow().connection(TnurccConnection::LeftAcw);

        // Test that left_edge was reconnected to the new edge
        assert!(
            std::ptr::eq(
                left_edge
                    .borrow()
                    .connection(TnurccConnection::RightCw)
                    .as_ref(),
                new_edge.as_ref()
            ),
            "Edge's left anti-clockwise connection was not correctly redirected."
        );
        // Test that right_edge was reconnected to the new edge
        assert!(
            std::ptr::eq(
                right_edge
                    .borrow()
                    .connection(TnurccConnection::LeftAcw)
                    .as_ref(),
                new_edge.as_ref()
            ),
            "Edge's right clockwise connection was not correctly redirected."
        );
        // Test that the new edge was connected to right_edge
        assert!(
            std::ptr::eq(
                right_edge.as_ref(),
                new_edge
                    .borrow()
                    .connection(TnurccConnection::RightCw)
                    .as_ref()
            ),
            "Edge's right clockwise connection was not correctly transfered."
        );
        // Test that the new edge was connected to left_edge
        assert!(
            std::ptr::eq(
                left_edge.as_ref(),
                new_edge
                    .borrow()
                    .connection(TnurccConnection::LeftAcw)
                    .as_ref()
            ),
            "Edge's left anti-clockwise connection was not correctly transfered."
        );
    }
}

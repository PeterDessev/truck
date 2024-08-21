use super::*;

impl<P> TnurccEdge<P> {
    pub fn new(
        index: usize,
        knot_interval: f64,
        origin: Rc<RefCell<TnurccControlPoint<P>>>,
        dest: Rc<RefCell<TnurccControlPoint<P>>>,
    ) -> Rc<RefCell<Self>> {
        let edge = TnurccEdge {
            index,
            connctions: [const { None }; 4],
            face_left: None,
            face_right: None,
            origin: Rc::clone(&origin),
            dest: Rc::clone(&dest),
            knot_interval,
        };
        let edge = Rc::new(RefCell::new(edge));

        origin.borrow_mut().valence += 1;
        origin.borrow_mut().incoming_edge = Some(Rc::clone(&edge));
        dest.borrow_mut().valence += 1;
        dest.borrow_mut().incoming_edge = Some(Rc::clone(&edge));

        edge.borrow_mut()
            .connctions
            .fill_with(|| Some(Rc::clone(&edge)));

        return edge;
    }

    /// Returns the connected edge.
    ///
    /// # Panics
    /// Panics if `self` was not correctly initialized or was mangled, resulting in a `None` connection.
    pub fn get_connection(&self, con: TnurccConnection) -> Rc<RefCell<TnurccEdge<P>>> {
        return Rc::clone(
            self.connctions[con as usize]
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
        return self.connctions[con as usize]
            .replace(other)
            .expect("TnurccEdge should always have a Some(connection)");
    }

    /// Returns the next anti-clockwise edge around `self`'s vertex `end`.
    pub fn acw_edge_from_point(&self, end: TnurccVertexEnd) -> Rc<RefCell<TnurccEdge<P>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match end {
            TnurccVertexEnd::Origin => TnurccConnection::RightAcw,
            TnurccVertexEnd::Dest => TnurccConnection::LeftAcw,
        };

        self.get_connection(dir)
    }

    /// Returns the next anti-clockwise edge around `self`'s face `side`.
    pub fn acw_edge_from_face(&self, side: TnurccFaceSide) -> Rc<RefCell<TnurccEdge<P>>> {
        // Determine which end the point is connected to on incoming_edge.
        let dir = match side {
            TnurccFaceSide::Left => TnurccConnection::LeftAcw,
            TnurccFaceSide::Right => TnurccConnection::RightAcw,
        };

        self.get_connection(dir)
    }

    /// Returns the side that `point` is located on, if any.
    /// 
    /// # Returns
    /// - `Some(end)` if `point` is connected to `self`.
    /// 
    /// - `None` otherwise.
    pub fn get_point_side(
        &self,
        point: Rc<RefCell<TnurccControlPoint<P>>>,
    ) -> Option<TnurccVertexEnd> {
        if std::ptr::eq(self.origin.as_ref(), point.as_ref()) {
            Some(TnurccVertexEnd::Origin)
        } else if std::ptr::eq(self.dest.as_ref(), point.as_ref()) {
            Some(TnurccVertexEnd::Dest)
        } else {
            None
        }
    }

    /// Returns the point on the end `end`.
    pub fn get_point(&self, end: TnurccVertexEnd) -> Rc<RefCell<TnurccControlPoint<P>>> {
        use TnurccVertexEnd::*;
        match end {
            Origin => Rc::clone(&self.origin),
            Dest => Rc::clone(&self.dest),
        }
    }

    /// Returns which side the face `face` is on, if it is on any.
    /// 
    /// # Returns
    /// - `Some(side)` if `face` is connected to `self`.
    /// 
    /// - `None` if `self` is not connected to `face`. 
    pub fn get_face_side(&self, face: Rc<RefCell<TnurccFace<P>>>) -> Option<TnurccFaceSide> {
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
    pub fn get_face(&self, side: TnurccFaceSide) -> Option<Rc<RefCell<TnurccFace<P>>>> {
        use TnurccFaceSide::*;
        match side {
            Left => self.face_left.as_ref().map(|f| Rc::clone(f)),
            Right => self.face_right.as_ref().map(|f| Rc::clone(f)),
        }
    }

    /// Automatically tries to connect two edges `first` and `other` that share at least one vertex and one face.
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
        for i in 0..self.connctions.len() {
            self.connctions[i] = None;
        }

        self.face_left = None;
        self.face_right = None;
    }
}

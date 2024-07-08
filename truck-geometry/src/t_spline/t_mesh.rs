use super::*;
use crate::errors::Error;
use std::fmt;

impl TMeshDirection {
    /// Returns an iterable object which rotates clockwise starting from UP.
    pub fn iter() -> impl Iterator<Item = TMeshDirection> {
        [
            TMeshDirection::UP,
            TMeshDirection::RIGHT,
            TMeshDirection::DOWN,
            TMeshDirection::LEFT,
        ]
        .iter()
        .copied()
    }

    /// Rotates `self` a quarter of a rotation clockwise.
    pub fn clockwise(self) -> Self {
        match self {
            TMeshDirection::UP => TMeshDirection::RIGHT,
            TMeshDirection::RIGHT => TMeshDirection::DOWN,
            TMeshDirection::DOWN => TMeshDirection::LEFT,
            TMeshDirection::LEFT => TMeshDirection::UP,
        }
    }

    /// Rotates `self` a quarter of a turn anti-clockwise.
    pub fn anti_clockwise(self) -> Self {
        match self {
            TMeshDirection::UP => TMeshDirection::LEFT,
            TMeshDirection::LEFT => TMeshDirection::DOWN,
            TMeshDirection::DOWN => TMeshDirection::RIGHT,
            TMeshDirection::RIGHT => TMeshDirection::UP,
        }
    }

    /// Flips `self`, rotating it half a turn.
    pub fn flip(self) -> Self {
        match self {
            TMeshDirection::UP => TMeshDirection::DOWN,
            TMeshDirection::DOWN => TMeshDirection::UP,
            TMeshDirection::LEFT => TMeshDirection::RIGHT,
            TMeshDirection::RIGHT => TMeshDirection::LEFT,
        }
    }

    /// Returns true if the direction is UP or DOWN
    pub fn virtical(self) -> bool {
        match self {
            TMeshDirection::UP => true,
            TMeshDirection::DOWN => true,
            TMeshDirection::LEFT => false,
            TMeshDirection::RIGHT => false,
        }
    }

    /// Returns true if the direction is RIGHT or LEFT
    pub fn horrizontal(self) -> bool {
        match self {
            TMeshDirection::UP => false,
            TMeshDirection::DOWN => false,
            TMeshDirection::LEFT => true,
            TMeshDirection::RIGHT => true,
        }
    }

    /// Returns true if a knot interval in the direction is a positive delta.
    pub fn knot_delta_positive(self) -> bool {
        match self {
            TMeshDirection::UP => true,
            TMeshDirection::DOWN => false,
            TMeshDirection::LEFT => false,
            TMeshDirection::RIGHT => true,
        }
    }

    /// Returns true if a knot interval in the direction is a negative delta.
    pub fn knot_delta_negative(self) -> bool {
        match self {
            TMeshDirection::UP => false,
            TMeshDirection::DOWN => true,
            TMeshDirection::LEFT => true,
            TMeshDirection::RIGHT => false,
        }
    }
}

impl fmt::Display for TMeshDirection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dir_string = match self {
            TMeshDirection::UP => String::from("up"),
            TMeshDirection::DOWN => String::from("down"),
            TMeshDirection::LEFT => String::from("left"),
            TMeshDirection::RIGHT => String::from("right"),
        };

        write!(f, "{dir_string}")
    }
}

impl<P> TMeshControlPoint<P> {
    /// Creates a new T-mesh control point located at the real space coordinate `p`, with edge conditions in all directions with knot interval `inverval`.
    pub fn new(p: P, inverval: f64) -> TMeshControlPoint<P> {
        TMeshControlPoint {
            point: p,
            connections: [
                Some((None, inverval)),
                Some((None, inverval)),
                Some((None, inverval)),
                Some((None, inverval)),
            ],
            knot_coordinates: (-1.0, -1.0),
        }
    }

    /// Returns an immutable reference to the location of the control point in real space.
    pub fn point(&self) -> &P {
        &self.point
    }

    // /// Returns an immutable refence to the connections array.
    // pub fn connections(&self) -> &[Option<TMeshConnection<P>>; 4] {
    //     &self.connections
    // }

    /// Get an immutable reference to the connection on the side `dir`.
    pub fn get(&self, dir: TMeshDirection) -> &Option<TMeshConnection<P>> {
        return &self.connections[dir as usize];
    }

    /// Get a mutable reference to the connection on the side `dir`.
    fn get_mut(&mut self, dir: TMeshDirection) -> &mut Option<TMeshConnection<P>> {
        return &mut self.connections[dir as usize];
    }

    /// Returns the knot coordinates for `self`
    pub fn get_knot_coordinates(&self) -> (f64, f64) {
        return self.knot_coordinates.clone();
    }

    /// Sets the knot coordinates for `self`. Only changes the coordinates if `self`
    /// is not connected to any other points or T-junctions. `t` is the horrizontal
    /// knot coordinate, and `s` is the virtical.
    ///
    /// # Returns
    /// - `TMeshExistingConnection` if `self` is connected to anything that is not an edge condition
    ///
    /// - `Ok` if the knot coordinates were changed.
    pub fn set_knot_coordinates(&mut self, t: f64, s: f64) -> Result<()> {
        // Ensure all points are edge conditions
        self.connections
            .iter()
            .all(|e| e.as_ref().is_some_and(|c| c.0.is_none()))
            .then(|| 0)
            .ok_or(Error::TMeshExistingConnection)?;

        self.knot_coordinates = (t, s);

        Ok(())
    }

    /// Sets the weight of the edge condition in the direction `dir` to weight `weight`.
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if the connection is T-junction.
    ///
    /// - `TMeshExistingConnection` if the connection is not an edge condition
    ///
    /// - `Ok` if the connection was modified.
    pub fn set_edge_con_weight(&mut self, dir: TMeshDirection, weight: f64) -> Result<()> {
        match self.get_mut(dir) {
            Some(connection) => {
                // If the connection is not an edge condition, return an error.
                if connection.0.is_some() {
                    return Err(Error::TMeshExistingConnection);
                }

                connection.1 = weight;
                return Ok(());
            }
            None => Err(Error::TMeshConnectionNotFound),
        }
    }

    /// Removes the connection in the direction `dir`.
    /// Modifies the connected point to also remove the connection.
    /// In the case of an error, nothing is modified.
    ///
    /// # Borrows
    /// The function must be able to mutably borrow the point self is connected to.
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if the connection does not exist.
    ///
    /// - `TMeshControlPointNotFound` if the connected control point exists and cannot be
    ///     borrowed mutably. (Does not return this error if the connection is an edge condition,
    ///     that is, if the point does not exist.)
    ///
    /// - `Ok` if the connection was successfully removed.
    pub fn remove_connection(&mut self, dir: TMeshDirection) -> Result<()> {
        match &mut self.connections[dir as usize] {
            Some(connection) => {
                // If the connection is not an edge condition, modify the connected point
                if connection.0.is_some() {
                    let mut borrow = connection
                        .0
                        .as_mut()
                        .unwrap()
                        .try_borrow_mut()
                        .map_err(|_| Error::TMeshControlPointNotFound)?;

                    // The connected point is connected to self on the opposite side
                    borrow.connections[dir.flip() as usize] = None;
                }

                self.connections[dir as usize] = None;
                return Ok(());
            }
            None => Err(Error::TMeshConnectionNotFound),
        }
    }

    /// Removes the edge condition in direction `dir` from a point, replacing it with a T-juction.
    ///
    /// # WARNING
    /// USE THIS FUNCTION WITH CARE. Using this function incorrectly will create bugs which
    /// are extremely difficult to squash, since many T-mesh functions rely on a properly
    /// formatted T-mesh and DO NOT CHECK to make sure they are given one.
    ///
    /// # Returns
    /// - `TMeshExistingConnection` if `dir` is not an edge condition.
    ///
    /// - `Ok` if the edge codition was successfully removed.
    pub fn remove_edge_condition(&mut self, dir: TMeshDirection) -> Result<()> {
        let is_edge = self.get_mut(dir).as_ref().is_some_and(|c| c.0.is_none());
        if is_edge {
            *self.get_mut(dir) = None;
            Ok(())
        } else {
            Err(Error::TMeshExistingConnection)
        }
    }

    /// Connect `point` to `other` in the direction `dir` and give the connection knot interval `ki`.
    /// `other` is also connected to `point` in the corresponding manner. Knot coordinates are calculated
    /// by taking the knot coordinates of `point` and applying the delta `ki` to the relevant coordinate.
    /// Only `other`'s knot coordinates will change
    ///
    /// # Borrows
    /// `connect` borrows both `point` and `other` mutably.
    ///
    /// # Returns
    /// - `TMeshControlPointNotFound` if either `point` or `other` could not be borrowed mutably.
    ///
    /// - `TMeshExistingConnection` if either point has an existing connection in the
    ///     corresponding directions.
    ///
    /// - `Ok` if the connection was successfully created between the two points.
    pub fn connect(
        point: Rc<RefCell<TMeshControlPoint<P>>>,
        other: Rc<RefCell<TMeshControlPoint<P>>>,
        dir: TMeshDirection,
        ki: f64,
    ) -> Result<()> {
        // is connection dir for point none?
        let con = {
            let borrow = point
                .try_borrow()
                .map_err(|_| Error::TMeshControlPointNotFound)?;

            borrow.get(dir).is_none()
        };

        // is connection dir.flip() for other none?
        let other_con = {
            let borrow = other
                .try_borrow()
                .map_err(|_| Error::TMeshControlPointNotFound)?;

            borrow.get(dir.flip()).is_none()
        };

        // If both points have no connections in the relevant directions, connect them together
        if con && other_con {
            // point -> other
            {
                let mut borrow = point
                    .try_borrow_mut()
                    .map_err(|_| Error::TMeshControlPointNotFound)?;

                borrow.connections[dir as usize] = Some((Some(Rc::clone(&other)), ki));
            }

            // point <-> other
            {
                let mut borrow = other
                    .try_borrow_mut()
                    .map_err(|_| Error::TMeshControlPointNotFound)?;

                // The connected point is connected to self on the opposite side
                borrow.connections[dir.flip() as usize] = Some((Some(Rc::clone(&point)), ki));
            }

            // Knot coordinates
            let mut delta = ki;
            other.borrow_mut().knot_coordinates = point.borrow_mut().knot_coordinates.clone();

            // Subtract the knot interval if needed (dir is LEFT or DOWN).
            if dir.knot_delta_negative() {
                delta *= -1.0;
            }

            // Delta the correct knot coordinate based on dir.
            if dir.horrizontal() {
                other.borrow_mut().knot_coordinates.0 += delta;
            } else {
                other.borrow_mut().knot_coordinates.1 += delta;
            }
        } else {
            // If either point has a connection in the relevant direction, return an error
            return Err(Error::TMeshExistingConnection);
        }

        Ok(())
    }

    /// Navigates from `self` in the direction `dir.anti_clockwise()` until a connection is found in the direction `dir`, 
    /// returning the point at which that connection was found.
    /// 
    /// # Returns 
    /// - `TMeshConnectionNotFound` if a T junction is found in the direction `dir.anti_clockwise()` while traversing.
    /// 
    /// - `TMeshControlPointNotFound` if an edge condition is found in the direction `dir.anti_clockwise()` while traversing.
    /// 
    /// - `Ok(Rc<RefCell<TMeshControlPoint<P>>>` if a connection was successfully found.
    pub fn navigate_until_con(&self, dir: TMeshDirection) -> Result<Rc<RefCell<Self>>> {
        let first = self.get(dir.anti_clockwise());

        // Check initial conditions
        if first.is_none() {
            return Err(Error::TMeshConnectionNotFound);
        }

        if first.as_ref().unwrap().0.is_none() {
            return Err(Error::TMeshControlPointNotFound);
        }

        // Begin traversing
        let mut cur_point = Rc::clone(&first.as_ref().unwrap().0.as_ref().unwrap());
        loop {
            if cur_point
                .borrow()
                .get(dir)
                .as_ref()
                .is_some_and(|c| c.0.is_some())
            {
                // Found the desired connection
                return Ok(cur_point);
            } else if cur_point.borrow().get(dir.anti_clockwise()).is_none() {
                // Encountered an unexpected T-junction
                return Err(Error::TMeshConnectionNotFound);
            } else if cur_point
                .borrow()
                .get(dir.anti_clockwise())
                .as_ref()
                .unwrap()
                .0
                .is_none()
            {
                // Encountered an unexpected edge condition
                return Err(Error::TMeshControlPointNotFound);
            }

            // Traverse to the next point
            cur_point = {
                let borrow = cur_point.borrow();

                Rc::clone(
                    borrow
                        .get(dir.anti_clockwise())
                        .as_ref()
                        .unwrap()
                        .0
                        .as_ref()
                        .unwrap(),
                )
            };
        }
    }
}

impl<P> fmt::Display for TMeshControlPoint<P>
where
    P: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Write self's point
        write!(f, "{:?} => {{\n", self.point())?;

        // Go through all directions for self
        for dir in TMeshDirection::iter() {
            // Write direction
            write!(f, "\t{}: ", dir)?;

            let con = self.get(dir);
            // If direction is T-junction
            if con.is_none() {
                write!(f, "~")?;
            } else {
                let con = con.as_ref().unwrap();
                // If con is edge condition
                if con.0.is_none() {
                    write!(f, "{}; Edge", con.1)?;
                } else {
                    // con is a connection to another point
                    let point_borrow = con.0.as_ref().unwrap().borrow();
                    let point = point_borrow.point();
                    write!(f, "{:?} => {}", point, con.1)?;
                }
            }
            write!(f, "\n")?;
        }
        write!(f, "}}\n")?;
        Ok(())
    }
}

impl<P> TMesh<P>
where
    P: PartialEq,
{
    /// Constructs a new rectangular T-mesh from four points in space and a value for
    /// outward-facing knot intervals. The result is the following mesh, where the
    /// numbers are the indecies of the array `points`. The knot interval between
    /// each point is 1.0.
    /// ```
    ///  3|   |2
    /// --+---+--
    ///   |   |
    /// --+---+--
    ///  0|   |1
    /// ```
    pub fn new(points: [P; 4], edge_knot_interval: f64) -> TMesh<P> {
        // Convert points into control points
        let control_points: Vec<Rc<RefCell<TMeshControlPoint<P>>>> = Vec::from(points)
            .into_iter()
            .map(|p| {
                let cont_point = TMeshControlPoint::new(p, edge_knot_interval);
                Rc::new(RefCell::new(cont_point))
            })
            .collect();

        // Set the first point as the "knot origin".
        control_points[0]
            .borrow_mut()
            .set_knot_coordinates(0.0, 0.0)
            .expect("No connections have been created for the current mesh");

        // Connect control points according to the diagram in the docs
        let mut dir = TMeshDirection::RIGHT;
        for i in 0..4 {
            control_points[i]
                .borrow_mut()
                .remove_edge_condition(dir)
                .expect("Point edge conditions are known at compile time");

            control_points[(i + 1) % 4]
                .borrow_mut()
                .remove_edge_condition(dir.flip())
                .expect("Point edge conditions are known at compile time");

            // Connect the point i to the point i plus one
            TMeshControlPoint::connect(
                Rc::clone(&control_points[i % 4]),
                Rc::clone(&control_points[(i + 1) % 4]),
                dir,
                1.0,
            )
            .expect("T-mesh connections are known valid at compile time");

            dir = dir.anti_clockwise();
        }

        return TMesh { control_points };
    }

    /// Returns an immutable reference to the control points vector
    pub fn control_points(&self) -> &Vec<Rc<RefCell<TMeshControlPoint<P>>>> {
        return &self.control_points;
    }

    /// Inserts a control point with real space coordinates `p` on the side `connection_side`
    /// of `con`. The knot interval of the connection between con and the new control point
    /// is the current weight of the connection multiplied by the ratio. Thus if ratio is
    /// 0.0, the connection between con and the new control point will have an interval of
    /// 0.0. `con` must be a control point in `self` and the new control point `p` must be
    /// inserted between two existing points, that is, `con`'s connection on the side
    /// `connection_side` must not be an edge condition or a T-junction.
    ///
    /// >NOTE!
    /// This will change the shape of the resulting surface.
    /// Use Local Knot Insertion in order to add a control point
    /// without changing the shape of the surface.
    ///
    /// # Errors
    /// - `TMeshInvalidKnotRatio` if `knot_ratio` is not in \[0.0, 1.0\].
    ///
    /// - `TMeshControlPointNotFound` if `con` is not a control point in the T-mesh.
    ///
    /// - `TMeshConnectionNotFound` if `con` has no connection on
    ///     `connection_side`, or if that connection is an edge condition.
    ///
    /// - `TMeshConnectionInvalidKnotInterval` if the connection between `con`
    ///     and the point in the direction `connection_side`, `con_side`, does not have the same
    ///     knot interval in both directions (`con` -> `con_side` != `con` <- `con_side`).
    ///     This should never happen.
    ///
    /// # Borrows
    /// Must be able to immutably borrow all points in the T-mesh,
    /// as well as mutably borrowing `con` and the point located in the direction `connection_side`
    ///
    /// # Panics
    /// Panics if any borrow does not succeed.
    pub fn add_control_point(
        &mut self,
        p: P,
        con: Rc<RefCell<TMeshControlPoint<P>>>,
        connection_side: TMeshDirection,
        knot_ratio: f64,
    ) -> Result<()> {
        // Check that the knot ratio is valid
        if 0.0 > knot_ratio || 1.0 < knot_ratio {
            return Err(Error::TMeshInvalidKnotRatio);
        }

        // If con is not found in the mesh, return the corresponding error.
        if self
            .control_points
            .iter()
            .position(|x| Rc::ptr_eq(x, &con))
            .is_none()
        {
            return Err(Error::TMeshControlPointNotFound);
        }

        // Return error if there is no connection or if the connection is an edge condition.
        if con
            .borrow()
            .get(connection_side)
            .as_ref()
            .map_or(true, |c| c.0.is_none())
        {
            return Err(Error::TMeshConnectionNotFound);
        }

        // Edge weights for p are set to 0.0, however, the final step will overwrite this
        // if a different edge weight was specified in the T-mesh constructor
        let p = Rc::new(RefCell::new(TMeshControlPoint::new(p, 0.0)));

        // Get the connection point
        let con_point = Rc::clone(&con);

        // Get the point currently connected to the connection point
        let other_point = {
            let borrow = con.borrow();
            let other_point = borrow
                .get(connection_side)
                .as_ref()
                .ok_or(Error::TMeshConnectionNotFound)?
                .0
                .as_ref()
                .ok_or(Error::TMeshControlPointNotFound)?;

            Rc::clone(other_point)
        };

        let knot_interval = con_point
            .borrow()
            .get(connection_side)
            .as_ref()
            .ok_or(Error::TMeshConnectionNotFound)?
            .1;

        let other_knot_interval = other_point
            .borrow()
            .get(connection_side.flip())
            .as_ref()
            .ok_or(Error::TMeshConnectionNotFound)?
            .1;

        // Confirm that the knot intervals are the same in both directions.
        if !(knot_interval - other_knot_interval).so_small() {
            return Err(Error::TMeshConnectionInvalidKnotInterval);
        }

        // Break connections between con_point and other_point
        con_point
            .borrow_mut()
            .remove_connection(connection_side)
            .expect("Guaranteed by previous checks");

        // Remove edge conditions for p
        p.borrow_mut()
            .remove_edge_condition(connection_side)
            .expect("New control point has known edge conditions");
        p.borrow_mut()
            .remove_edge_condition(connection_side.flip())
            .expect("New control point has known edge conditions");

        // Insert p with the proper knot intervals.
        // con <-> other becomes con <-> p <-> other
        // con <-> p
        TMeshControlPoint::connect(
            Rc::clone(&con_point),
            Rc::clone(&p),
            connection_side,
            knot_interval * knot_ratio,
        )
        .map_err(|_| Error::TMeshUnkownError)?;

        // p <-> other
        TMeshControlPoint::connect(
            Rc::clone(&p),
            Rc::clone(&other_point),
            connection_side,
            knot_interval * (1.0 - knot_ratio),
        )
        .map_err(|_| Error::TMeshUnkownError)?;

        // When a new point is added, there can only possibly be edge conditions on
        // the two sides perpendicular to the connection. If there is no edge condition,
        // Rule 2 for T-meshes [Sederberg et al. 2003] should be checked to find any
        // inferred connections (ic), and if it does not apply, the connection is removed.

        // TODO: Currently this code does not allow for knot intervals of 0, and needs to be
        // updated once a solution to figure 9 in [Sederberg et al. 2003] is found.
        let cw_con = {
            // Borrow for lifetimes
            let borrow = con.borrow();

            // Get the connection in the correct direction
            let connection = borrow.get(connection_side.clockwise()).as_ref();

            // Check if connection is an edge condition
            let edge_con = connection.clone().is_some_and(|c| c.0.is_none());

            // If so, return the edge weight with it, otherwise return whatever.
            let weight = if edge_con {
                connection
                    .expect("Cloned option was previously unwrapped")
                    .1
            } else {
                0.0
            };

            (edge_con, weight)
        };
        if cw_con.0 {
            // Should never return an error
            p.borrow_mut()
                .set_edge_con_weight(connection_side.clockwise(), cw_con.1)
                .map_err(|_| Error::TMeshUnkownError)?;
        } else {
            // Remove the edge condition created by the constructor.
            let _ = p
                .borrow_mut()
                .remove_edge_condition(connection_side.clockwise());

            // If a point that satisfies Rule 2 from [Sederberg et al. 2003] is found, connect it.
            // Should also never return an error.
            self.find_inferred_connection(Rc::clone(&p), connection_side.clockwise())
                .map_err(|_| Error::TMeshUnkownError)?;
        }

        let acw_con = {
            // Borrow for lifetimes
            let borrow = con.borrow();

            // Get the connection in the correct direction
            let connection = borrow.get(connection_side.anti_clockwise()).as_ref();

            // Check if connection is an edge condition
            let edge_con = connection.clone().is_some_and(|c| c.0.is_none());

            // If so, return the edge weight with it, otherwise return whatever.
            let weight = if edge_con {
                connection
                    .expect("Cloned option was previously unwrapped")
                    .1
            } else {
                0.0
            };

            (edge_con, weight)
        };
        if acw_con.0 {
            // Should never return an error
            p.borrow_mut()
                .set_edge_con_weight(connection_side.anti_clockwise(), acw_con.1)
                .map_err(|_| Error::TMeshUnkownError)?;
        } else {
            // Remove the edge condition created by the constructor.
            let _ = p
                .borrow_mut()
                .remove_edge_condition(connection_side.anti_clockwise());

            // If a point that satisfies Rule 2 from [Sederberg et al. 2003] is found, connect it.
            // Should also never return an error.
            self.find_inferred_connection(Rc::clone(&p), connection_side.anti_clockwise())
                .map_err(|_| Error::TMeshUnkownError)?;
        }

        self.control_points.push(p);
        Ok(())
    }

    /// Finds the first point that was added to a T-mesh with a specific cartesian coordinate
    pub fn find(&self, p: P) -> Result<Rc<RefCell<TMeshControlPoint<P>>>> {
        Ok(Rc::clone(
            self.control_points()
                .iter()
                .find(|x| *x.borrow().point() == p)
                .ok_or(Error::TMeshControlPointNotFound)?,
        ))
    }


    /// Finds and creates an inferred connection on the point `p` for the anti-clockwise
    /// face which `face_dir` points into the face and which `p` is a part of. `p` must be part of
    /// a valid face and must not be a corner (a connection cannot already exist in the `face_dir`
    /// direction.)
    ///
    /// > **Warning**\
    /// > Does not check if the face is valid.
    ///
    ///
    /// Example mesh for reference:
    /// ```
    /// +----+-+-|+|-----{+}
    /// |    |    ^       |
    /// +----+---[+]-+---<+>
    /// |            |    |
    /// +-+----+-----+----+
    /// ```
    /// - `face_dir` points up
    /// - `[+]` is `p`
    /// - `<+>` and `{+}` are used in the internal comments
    ///
    /// `p`, labeled `[+]`, will be connected to `|+|` after calling `find_inferred_connection`
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if any connection that is expected to
    ///     exist does not. This should only happen on a malformed T-mesh.
    ///
    /// - `TMeshControlPointNotFound` if any control point that is expected
    ///     to exist does not. This usually happens because the current face does not exist
    ///     (`p` is an edge condition).
    ///
    /// - `TMeshExistingConnection` if a connection exists in the `face_dir` direction
    ///     (`p` is a corner).
    ///
    /// - `Ok(true)` if an inferred connection was found and connected.
    ///
    /// - `Ok(false)` if an inferred connection was not found.
    ///
    /// # Borrows
    /// Immutably borrows all points along the anti-clockwise face path between
    /// `p` and `|+|`.
    ///
    /// Mutably borrows `p` and `|+|`.
    ///
    /// # Panics
    /// If `p` or the potential point to which the inferred connection will go to
    /// cannot be borrowed mutably, `find_inferred_connection` will panic.
    ///
    /// # Zero Knot Intervals
    /// Currently this function is not designed to deal with zero knot intervals,
    /// and may not produce the expected result with them.
    fn find_inferred_connection(
        &mut self,
        p: Rc<RefCell<TMeshControlPoint<P>>>,
        face_dir: TMeshDirection,
    ) -> Result<bool> {
        let mut cur_point = Rc::clone(&p);
        let mut cur_dir = face_dir.clockwise();
        let mut ic_knot_measurment = 0.0; // The distance traversed from p to <+>
        let mut ic_knot_interval = 0.0; // The interval of the ic

        // Check that p is not a corner
        if p.borrow()
            .get(face_dir)
            .as_ref()
            .is_some_and(|c| c.0.is_some())
        {
            return Err(Error::TMeshExistingConnection);
        }

        // Traverse in the direction cur_dir until an anti-clockwise connection is found.
        // Repeat once to get to the point {+}
        for i in 0..2 {
            let mut accumulation = 0.0;

            'traverse: loop {
                // Accumulate knot intervals on the side of a face
                accumulation += cur_point
                    .borrow()
                    .get(cur_dir)
                    .as_ref()
                    .ok_or(Error::TMeshConnectionNotFound)?
                    .1;

                // Traverse to the next control point
                cur_point = {
                    let borrow = cur_point.borrow();

                    let point = borrow
                        .get(cur_dir)
                        .as_ref()
                        .ok_or(Error::TMeshConnectionNotFound)?
                        .0
                        .as_ref()
                        .ok_or(Error::TMeshControlPointNotFound)?;

                    Rc::clone(&point)
                };

                // Face corner detection. Break if a corner is detected. The and in
                // is_some_and is a formality which shouldn't be nessessary.
                // (needs testing)
                if cur_point
                    .borrow()
                    .get(cur_dir.anti_clockwise())
                    .as_ref()
                    .is_some_and(|c| c.0.is_some())
                {
                    cur_dir = cur_dir.anti_clockwise();
                    break 'traverse;
                }
            }

            if i == 0 {
                // Accumulate knot intevals for comparison later. Only accumulate knots that are
                // related to the current face
                ic_knot_measurment = accumulation;
            } else if i == 1 {
                // Accumulate knot intervals for the potential IC knot weight. Only accumulate
                // knots that are related to the current face
                ic_knot_interval = accumulation;
            }
        }

        // After the above loop, cur_point is located at {+} and cur_dir points opposite
        // connection_side. Start accumulating knot intervals until the edge of the face
        // is reached, the accumulation is greater than the measurement, or the two are equal.
        let mut ic_knot_accumulation = 0.0;
        loop {
            // Ic found
            if (ic_knot_measurment - ic_knot_accumulation).so_small() {
                TMeshControlPoint::connect(
                    Rc::clone(&p),
                    Rc::clone(&cur_point),
                    cur_dir.clockwise(),
                    ic_knot_interval,
                )
                .map_err(|_| Error::TMeshUnkownError)?;
                return Ok(true);

            // Ic not possible, knot accumulation surpassed measurment or reached face corner.
            // Shouldn't need corner detection due to rule 1 in [Sederberg et al. 2003].
            // (needs testing)
            } else if ic_knot_accumulation > ic_knot_measurment
                || cur_point
                    .borrow()
                    .get(cur_dir.anti_clockwise())
                    .as_ref()
                    .map_or(true, |c| c.0.is_none())
            {
                return Ok(false);
            }

            ic_knot_accumulation += cur_point
                .borrow()
                .get(cur_dir)
                .as_ref()
                .ok_or(Error::TMeshConnectionNotFound)?
                .1;

            cur_point = {
                let borrow = cur_point.borrow();

                let point = borrow
                    .get(cur_dir)
                    .as_ref()
                    .ok_or(Error::TMeshConnectionNotFound)?
                    .0
                    .as_ref()
                    .ok_or(Error::TMeshControlPointNotFound)?;

                Rc::clone(&point)
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Constructs the following T-mesh  using various constructors and expecting certain
    /// connections to be automatically created according to the rules that govern a
    /// T-mesh as enumerated in  \[Sederberg et al. 2003\]. The '!' character indicates
    /// that an edge will not be explicitly created, but is required to exist by the T-mesh rules.
    ///
    /// ```
    ///   |   |   |
    /// --+---+---+-- 2
    ///   |   !   |
    ///   |   +---+-- 1
    ///   |   !   |
    /// --+---+---+-- 0
    ///   |   |   |
    ///   0   2   4
    /// ```
    // fn construct_test_tmesh() {
    // let mesh = TMesh::new(Point3::from((0.0, 0.0, 0.0)));

    // // Add control points starting from the top left, going clockwise
    // mesh.add(mesh.get((0, 0, 0)), (0, 2, 0), TMeshDirection::UP, 2)
    //     .unwrap();
    // control_points.push(control_points[0].connect_new((0, 2, 0), TMeshDirection::UP, 2));
    // control_points.push(control_points[0].connect_new((2, 0, 0), TMeshDirection::RIGHT, 2));

    // let other_control_point = TMeshControlPoint::from(());
    // mesh.add_knot()
    // }

    /// Returns a result which provides information regarding the connection of two points on
    /// `point`'s connection in the direction `dir`.
    ///
    /// # Returns.
    /// - `(0, ERROR)` when `point`'s connection is invalid.
    /// - `(1, ERROR)` when `other`'s connection is invalid.
    ///
    /// - `(#, TMeshConnectionNotFound)` when the connection is a T-mesh.
    /// - `(#, TMeshControlPointNotFound)` when the connection is an edge condition.
    /// - `(#, TMeshExistingConnection)` when the connection does not lead to the correct point.
    ///
    /// - `Ok(())` if the connection is correctly configured.
    fn test_points_are_connected<P: PartialEq>(
        point: Rc<RefCell<TMeshControlPoint<P>>>,
        other: Rc<RefCell<TMeshControlPoint<P>>>,
        dir: TMeshDirection,
    ) -> std::result::Result<(), (i32, Error)> {
        // Check that point is connected to other
        let point_borrow = point.borrow();
        let point_con = point_borrow
            .get(dir)
            .as_ref()
            .ok_or((0, Error::TMeshConnectionNotFound))?
            .0
            .as_ref()
            .ok_or((0, Error::TMeshControlPointNotFound))?;
        let point_equal = Rc::ptr_eq(point_con, &other);
        point_equal
            .then(|| 0)
            .ok_or((0, Error::TMeshExistingConnection))?;

        // Check that other is connected to point
        let other_borrow = other.borrow();
        let other_con = other_borrow
            .get(dir.flip())
            .as_ref()
            .ok_or((1, Error::TMeshConnectionNotFound))?
            .0
            .as_ref()
            .ok_or((1, Error::TMeshControlPointNotFound))?;
        let other_equal = Rc::ptr_eq(other_con, &point);
        other_equal
            .then(|| 0)
            .ok_or((1, Error::TMeshExistingConnection))?;
        Ok(())
    }

    /// Tests the construction of a new T-mesh, verifying that all the points are correctly connected and exist.
    #[test]
    fn test_t_mesh_new() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mesh = TMesh::new(points, 1.0);

        // Test that there are four control points in the mesh after creation.
        assert!(
            mesh.control_points().len() == 4,
            "T-mesh retained {} of 4 points during creation",
            mesh.control_points.len(),
        );

        // Test that the origin and the right are correctly connected
        let con_test = test_points_are_connected(
            mesh.find(Point3::from((0.0, 0.0, 0.0))).unwrap(),
            mesh.find(Point3::from((1.0, 0.0, 0.0))).unwrap(),
            TMeshDirection::RIGHT,
        );
        assert!(
            con_test.is_ok(),
            "The origin is not correctly connected to (1, 0, 0)"
        );

        // Test that the origin and the up are correctly connected
        let con_test: std::result::Result<(), (i32, Error)> = test_points_are_connected(
            mesh.find(Point3::from((0.0, 0.0, 0.0))).unwrap(),
            mesh.find(Point3::from((0.0, 1.0, 0.0))).unwrap(),
            TMeshDirection::UP,
        );
        assert!(
            con_test.is_ok(),
            "The origin is not correctly connected to (0, 1, 0)"
        );

        // Test that (1,1,0) and the up are correctly connected
        let con_test: std::result::Result<(), (i32, Error)> = test_points_are_connected(
            mesh.find(Point3::from((1.0, 1.0, 0.0))).unwrap(),
            mesh.find(Point3::from((0.0, 1.0, 0.0))).unwrap(),
            TMeshDirection::LEFT,
        );
        assert!(
            con_test.is_ok(),
            "(1, 1, 0) is not correctly connected to (0, 1, 0)"
        );

        // Test that (1,1,0) and the right are correctly connected
        let con_test: std::result::Result<(), (i32, Error)> = test_points_are_connected(
            mesh.find(Point3::from((1.0, 1.0, 0.0))).unwrap(),
            mesh.find(Point3::from((1.0, 0.0, 0.0))).unwrap(),
            TMeshDirection::DOWN,
        );
        assert!(
            con_test.is_ok(),
            "(1, 1, 0) is not correctly connected to (1, 0, 0)"
        );
    }

    /// Constructs a T-mesh, testing that inserting a new control point with no inferred connections
    /// produces the correct result.
    ///
    /// ```
    ///    |  |  |
    ///  --+-[+]-+--
    ///    |     |
    ///  --+-----+--
    ///    |     |
    /// ```
    /// `[+]` is the inserted control point, which is tested. Testing includes verifying conenctions to other points,
    /// making sure the T-junction in the `DOWN` direction is correct, and verifying the edge condition.
    #[test]
    fn test_t_mesh_insert_control_point() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);

        mesh.add_control_point(
            Point3::from((0.5, 1.0, 0.0)),
            mesh.find(Point3::from((0.0, 1.0, 0.0)))
                .expect("Point (0, 1, 0) is a valid point in the T-mesh"),
            TMeshDirection::RIGHT,
            0.5,
        )
        .expect("Arguments provided to add_control_point are valid and insertion is allowed");

        let top_left = mesh.find(Point3::from((0.0, 1.0, 0.0))).unwrap();
        let top_mid = mesh.find(Point3::from((0.5, 1.0, 0.0))).unwrap();
        let top_right = mesh.find(Point3::from((1.0, 1.0, 0.0))).unwrap();

        // Test that there are five control points in the mesh after insertion.
        assert!(
            mesh.control_points().len() == 5,
            "Inserted control point was not added to control_points vector"
        );

        // Test that the left and the middle are correctly connected
        let left_mid_con = test_points_are_connected(
            Rc::clone(&top_left),
            Rc::clone(&top_mid),
            TMeshDirection::RIGHT,
        );
        assert!(
            left_mid_con.is_ok(),
            "Top left and top middle points are not correctly connected"
        );

        // Test that the right and the middle are correctly connected
        let right_mid_con = test_points_are_connected(
            Rc::clone(&top_right),
            Rc::clone(&top_mid),
            TMeshDirection::LEFT,
        );
        assert!(
            right_mid_con.is_ok(),
            "Top left and top middle points are not correctly connected"
        );

        // Check edge condition for the middle
        assert!(
            top_mid
                .borrow()
                .get(TMeshDirection::UP)
                .as_ref()
                .is_some_and(|c| c.0.is_none() && c.1 == 1.0),
            "Top middle edge condition (direction UP) is incorrectly configured"
        );

        // Check T-junction for the middle
        assert!(
            top_mid.borrow().get(TMeshDirection::DOWN).is_none(),
            "Top middle T-junction (direction DOWN) is incorrectly configured"
        );
    }

    /// Constructs a T-mesh, testing that inserting a new control point with one inferred connection
    /// produces the correct result.
    ///
    /// ```
    ///    |  |  |
    ///  --+--+--+--
    ///    |  :  |
    ///  --+-[+]-+--
    ///    |  |  |
    /// ```
    /// `[+]` is the inserted control point, which is tested. The control point is inserted on the `RIGHT`
    /// connection of the bottom left point, and the connection marked `:` is the inferred connection which
    /// should exist after `[+]` is inserted.
    #[test]
    fn test_t_mesh_insert_control_point_one_inferred_connection() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);

        // Add the first control points
        mesh.add_control_point(
            Point3::from((0.5, 1.0, 0.0)),
            mesh.find(Point3::from((0.0, 1.0, 0.0)))
                .expect("Point (0, 1, 0) is a valid point in the T-mesh"),
            TMeshDirection::RIGHT,
            0.5,
        )
        .expect("Arguments provided to add_control_point are valid and insertion is allowed");

        // Add second control point with inferred connection
        mesh.add_control_point(
            Point3::from((0.5, 0.0, 0.0)),
            mesh.find(Point3::from((0.0, 0.0, 0.0)))
                .expect("Point (0, 0, 0) is a valid point in the T-mesh"),
            TMeshDirection::RIGHT,
            0.5,
        )
        .expect("Arguments provided to add_control_point are valid and insertion is allowed");

        let top_mid = mesh.find(Point3::from((0.5, 1.0, 0.0))).unwrap();
        let bottom_mid = mesh.find(Point3::from((0.5, 0.0, 0.0))).unwrap();

        // Test that the inferrect connection exists
        let inferred_con_exist = test_points_are_connected(
            Rc::clone(&bottom_mid),
            Rc::clone(&top_mid),
            TMeshDirection::UP,
        );
        assert!(
            inferred_con_exist.is_ok(),
            "Inferred connection is not correctly configured"
        );

        // Test that inferred connection knot interval is correctly configured
        let inferred_con_interval = {
            let borrow = top_mid.borrow();

            borrow
                .get(TMeshDirection::DOWN)
                .as_ref()
                .expect("Connection should exist")
                .1
                == 1.0
        };
        assert!(
            inferred_con_interval,
            "Inferred connection knot interval is incorrect"
        );
    }

    /// Constructs a T-mesh, testing that inserting a new control point with two inferred connections
    /// produces the correct result.
    ///
    /// ```
    ///    |  |  |
    ///  --+-<+>-+--
    ///    |  |  |
    ///  --+~[+]~+--
    ///    |  |  |
    ///  --+--+--+--
    ///    |  |  |
    /// ```
    /// `[+]` is the inserted control point, which is tested. The control point is inserted on the `DOWN` connection of `<+>`, and the connections marked `~` are inferred connections which should exist after `[+]` is inserted.
    #[test]
    fn test_t_mesh_insert_control_point_two_inferred_connections() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);

        // Add the four control points
        let points = [
            ((0.5, 0.0, 0.0), (0.0, 0.0, 0.0)), // bottom mid, connects to (0, 0, 0) from its right
            ((1.0, 0.5, 0.0), (1.0, 0.0, 0.0)), // right mid,  connects to (1, 0, 0) from its up
            ((0.5, 1.0, 0.0), (1.0, 1.0, 0.0)), // top mid,    connects to (1, 1, 0) from its left
            ((0.0, 0.5, 0.0), (0.0, 1.0, 0.0)), // right mid,  connects to (0, 1, 0) from its down
        ];
        let mut dir = TMeshDirection::RIGHT;

        for point_pair in points {
            mesh.add_control_point(
                Point3::from(point_pair.0),
                mesh.find(Point3::from(point_pair.1)).expect(&format!(
                    "Point {:?} is a valid point in the T-mesh",
                    point_pair.1
                )),
                dir,
                0.5,
            )
            .expect("Arguments provided to add_control_point are valid and insertion is allowed");
            dir = dir.anti_clockwise();
        }

        // Add center control point with inferred connections
        mesh.add_control_point(
            Point3::from((0.5, 0.5, 0.0)),
            mesh.find(Point3::from((0.5, 0.0, 0.0)))
                .expect("Point (0.5, 0, 0) is a valid point in the T-mesh"),
            TMeshDirection::UP,
            0.5,
        )
        .expect("Arguments provided to add_control_point are valid and insertion is allowed");

        let middle = mesh.find(Point3::from((0.5, 0.5, 0.0))).unwrap();

        // Test connections in the four directions
        let left_mid_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((0.5, 1.0, 0.0))).unwrap()),
            TMeshDirection::UP,
        );
        assert!(
            left_mid_con.is_ok(),
            "Middle is not correctly connected to UP"
        );

        let left_mid_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((1.0, 0.5, 0.0))).unwrap()),
            TMeshDirection::RIGHT,
        );
        assert!(
            left_mid_con.is_ok(),
            "Middle is not correctly connected to RIGHT"
        );

        let left_mid_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((0.5, 0.0, 0.0))).unwrap()),
            TMeshDirection::DOWN,
        );
        assert!(
            left_mid_con.is_ok(),
            "Middle is not correctly connected to DOWN"
        );

        let left_mid_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((0.0, 0.5, 0.0))).unwrap()),
            TMeshDirection::LEFT,
        );
        assert!(
            left_mid_con.is_ok(),
            "Middle is not correctly connected to LEFT"
        );
    }
}

use super::*;
use crate::errors::Error;
use std::fmt;

impl<P> TMesh<P> {
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

        // Set the first point as the "knot origin". This may result in some negative components in the
        // knot vectors of the points near the left and bottom edge condition, but this should not matter (test?)
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

        return TMesh {
            control_points,
            knot_vectors: None,
        };
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
    /// # Returns
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
    /// - `Ok(())` if the control point was successfully added
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

        // Mark existing knot vectors as stale
        self.knot_vectors = None;

        // Edge weights for p are set to 0.0, however, the final step will overwrite this
        // if a different edge weight was specified in the T-mesh constructor
        let p = Rc::new(RefCell::new(TMeshControlPoint::new(p, 0.0)));

        // Get the connection point
        let con_point = Rc::clone(&con);

        // Get the point currently connected to the connection point
        let other_point = {
            let borrow = con.borrow();
            Rc::clone(&borrow.get_conected_point(connection_side)?)
        };

        let knot_interval = con_point
            .borrow()
            .get_con_knot(connection_side)
            .ok_or(Error::TMeshConnectionNotFound)?;

        let other_knot_interval = other_point
            .borrow()
            .get_con_knot(connection_side.flip())
            .ok_or(Error::TMeshConnectionNotFound)?;

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

        // Add control point
        self.control_points.push(p);

        // Regenerate knot vectors (See comment on TMesh.knot_vectors is mod.rs)
        self.generate_knot_vectors()
            .map_err(|_| Error::TMeshMalformedMesh)?;
        Ok(())
    }

    /// Attemps to add a control point to the mesh given the cartesian point `p` and the absolute knot coordinates `knot_coords`
    /// in the form `(s, t)`. In order for insertion to succeed, there must either be an S or T edge located at the parametric
    /// point `knot_coords` in the mesh `self`. Note that zero knot insertions will return an error, as the side on which to
    /// insert the zero knot is ambiguous.
    ///
    /// # Returns
    /// - `TMeshConnectionInvalidKnotInterval` if either knot coordinate in `knot_coords` is not in the range (0, 1).
    ///
    /// - `TMeshExistingControlPoint` if a control point already exists at parametric coordinates `knot_coords`.
    ///
    /// - `TMeshMalformedMesh` if multiple edges are found which intersect the location of the new point.
    ///
    /// - `TMeshConnectionNotFound` if no edges are found which intersect the location of the new point.
    ///
    /// - `Ok(())` if the control point was successfully added.
    ///
    /// # Borrows
    /// Immutably borrows every point in the mesh `self`.
    pub fn try_add_absolute_point(&mut self, p: P, knot_coords: (f64, f64)) -> Result<()> {
        // Make sure desred knot coordinates are within msh bounds
        if knot_coords.0 < 0.0 || knot_coords.0 > 1.0 || knot_coords.1 < 0.0 || knot_coords.1 > 1.0
        {
            return Err(Error::TMeshConnectionInvalidKnotInterval);
        }

        // If a point already exists at the desired knot coordinates, return an error. Zero knot intervals can be put
        // on any side of a point and still have the same knot coordinates, but the structure of the mesh will not be
        // different. Thus, zero knot insertion must be done manually.
        if self
            .control_points
            .iter()
            .find(|c| {
                let c_coords = c.borrow().get_knot_coordinates();
                let comparison = (c_coords.0 - knot_coords.0, c_coords.1 - knot_coords.1);
                comparison.0.so_small() && comparison.1.so_small()
            })
            .is_some()
        {
            return Err(Error::TMeshExistingControlPoint);
        }

        // The function checks for any T or S edges that intersect the point in paramtric space where the
        // point is to be insertet, then computes the knot ratio needed such that the point is inserted
        // at the correct place and inserts it using add_control_point.

        // Check for any T edges which intersect the parametric location of the new point.
        let mut point_t_coord = 0.0;
        let mut con_knot = 0.0;
        let s_axis_stradle_points = self
            .control_points
            .iter()
            // Filter all points along the S axis of inserton
            .filter(|point| (point.borrow().get_knot_coordinates().0 - knot_coords.0).so_small())
            // Filter those points to only include the point that stradles the T axis of insertion
            .filter(|point| {
                if let Some(con) = point.borrow().get(TMeshDirection::UP) {
                    let temp_t_coord = point.borrow().get_knot_coordinates().1;
                    let temp_inter = con.1;

                    // Knot of the new point is located on the connection being investigated?
                    if temp_t_coord < knot_coords.1 && temp_t_coord + temp_inter > knot_coords.1 {
                        point_t_coord = temp_t_coord; // T coordinate of the current point
                        con_knot = temp_inter; // Edge knot interval

                        return true;
                    }
                }
                false
            })
            .map(|point| Rc::clone(point))
            .collect::<Vec<Rc<RefCell<TMeshControlPoint<P>>>>>();

        // Depending on the number of points whose connections intersect the location of the new point,
        // different errors or actions are taken
        match s_axis_stradle_points.len() {
            // No T-edge instersects the point where the point needs to be inserted,
            // try to find an S edge which intersects the location of the point
            0 => {}
            1 => {
                // A T-edge is found where the point intersects
                return self
                    .add_control_point(
                        p,
                        Rc::clone(&s_axis_stradle_points[0]),
                        TMeshDirection::UP,
                        (knot_coords.1 - point_t_coord) / con_knot,
                    )
                    .map_err(|_| Error::TMeshUnkownError);
            }
            _ => {
                // Multiple T-edges are found where the point intersects (Should never happen)
                return Err(Error::TMeshMalformedMesh);
            }
        };

        let mut point_s_coord = 0.0;
        let mut con_knot = 0.0;
        let t_axis_stradle_points = self
            .control_points
            .iter()
            // Filter all points along the T axis of inserton
            .filter(|point| (point.borrow().get_knot_coordinates().1 - knot_coords.1).so_small())
            // Filter those points to only include the point that stradles the S axis of insertion
            .filter(|point| {
                if let Some(con) = point.borrow().get(TMeshDirection::RIGHT) {
                    let temp_s_coord = point.borrow().get_knot_coordinates().0;
                    let temp_inter = con.1;

                    // Knot of the new point is located on the connection being investigated?
                    if temp_s_coord < knot_coords.0 && temp_s_coord + temp_inter > knot_coords.0 {
                        point_s_coord = temp_s_coord; // S coordinate of the current point
                        con_knot = temp_inter; // Edge knot interval

                        return true;
                    }
                }
                false
            })
            .map(|point| Rc::clone(point))
            .collect::<Vec<Rc<RefCell<TMeshControlPoint<P>>>>>();

        // Depending on the number of points whose connections intersect the location of the new point,
        // different errors or actions are taken
        match t_axis_stradle_points.len() {
            0 => {
                // No S-edge instersects the point where the point needs to be inserted, return an error
                return Err(Error::TMeshConnectionNotFound);
            }
            1 => {
                // An S-edge is found where the point intersects
                return self
                    .add_control_point(
                        p,
                        Rc::clone(&t_axis_stradle_points[0]),
                        TMeshDirection::RIGHT,
                        (knot_coords.0 - point_s_coord) / con_knot,
                    )
                    .map_err(|_| Error::TMeshUnkownError);
            }
            _ => {
                // Multiple S-edges are found where the point intersects (Should never happen)
                return Err(Error::TMeshMalformedMesh);
            }
        };
    }

    /// Generates the S and T knot vectors for a particular point. The returned tuple is of the form `(S_vector, T_vector)`,
    /// where `S_vector` is the horizontal knot vector and `T_vector` is the virtical knot vector.
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if a T-junction is unexpectedly found (non-rectangular face)
    ///
    /// - `TMeshControlPointNotFound` if an edge conditon is unexpectedly found (internal edge condition)
    ///
    /// - `Ok((KnotVeec, KnotVec))` if knot vectors are successfully generated
    ///
    /// # Borrows
    ///
    fn get_point_knot_vectors(p: Rc<RefCell<TMeshControlPoint<P>>>) -> Result<(KnotVec, KnotVec)> {
        let mut s_vec: Vec<f64> = vec![0.0; 5];
        let mut t_vec: Vec<f64> = vec![0.0; 5];

        // Center of the knot vec is the knot coordinate of the current point
        s_vec[2] = p.borrow().get_knot_coordinates().0;
        t_vec[2] = p.borrow().get_knot_coordinates().1;

        // Cast rays in all directions
        for dir in TMeshDirection::iter() {
            let cur_point = Rc::clone(&p);
            // Knot intervals for intersections (These are deltas, not absolutes)
            let knot_intervals = TMesh::cast_ray(cur_point, dir, 2)?;

            for i in 0..2 {
                let inter = knot_intervals[i];

                // Knot vectors for a point go left to right and lower to upper as the index increases.
                // Knot interval will be the knot interval from the center point to the i'th point in the direction dir.
                // (The mesh will most likely look different, with T junctions and edge conditions)
                //           [T]    Initial cur_point
                //            + 4  /
                //            |   /
                //            + 3/
                //            | /
                //  +----+----+----+----+  [S]
                //  0    1    |    3    4
                //            + 1
                //            |
                //            + 0
                match dir {
                    TMeshDirection::UP => {
                        t_vec[3 + i] = t_vec[2 + i] + inter;
                    }
                    TMeshDirection::RIGHT => {
                        s_vec[3 + i] = s_vec[2 + i] + inter;
                    }
                    TMeshDirection::DOWN => {
                        t_vec[1 - i] = t_vec[2 - i] - inter;
                    }
                    TMeshDirection::LEFT => {
                        s_vec[1 - i] = s_vec[2 - i] - inter;
                    }
                }
            }
        }
        return Ok((KnotVec::from(s_vec), KnotVec::from(t_vec)));
    }

    /// Generates the knot vectors for each control point using the method in \[Sederberg et al. 2003\].
    /// The knot vector for a control point is located at the same index as the control point is in `self.control_points`.
    /// Each pair of knot vectors is arranged as `(s, t)` where `s` is the horizontal and `t` is the virtical.
    ///
    /// # Returns
    /// All errors returned from the function result from a malformed T-mesh and should not
    /// - `TMeshConnectionNotFound` if a non-rectangular face is encountered.
    ///
    /// - `TMeshControlPointNotFound` if an unexpected edge condition is found.
    ///
    /// - `Ok(())` if knot vectors are successfully generated.
    ///
    /// # Borrows
    /// Immutably borrows every point in `self.control_points`.
    fn generate_knot_vectors(&mut self) -> Result<()> {
        let mut knot_vecs: Vec<(KnotVec, KnotVec)> = Vec::new();

        for control_point in self.control_points.iter() {
            knot_vecs.push(TMesh::get_point_knot_vectors(Rc::clone(&control_point))?);
        }

        self.knot_vectors = Some(knot_vecs);
        Ok(())
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
        if p.borrow().con_type(face_dir) == TMeshConnectionType::Point {
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
                    .get_con_knot(cur_dir)
                    .ok_or(Error::TMeshConnectionNotFound)?;

                // Traverse to the next control point
                cur_point = {
                    let borrow = cur_point.borrow();
                    borrow.get_conected_point(cur_dir)?
                };

                // Face corner detection. Break if a corner is detected.
                if cur_point.borrow().con_type(cur_dir.anti_clockwise())
                    == TMeshConnectionType::Point
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
            ic_knot_accumulation += cur_point
                .borrow()
                .get_con_knot(cur_dir)
                .ok_or(Error::TMeshConnectionNotFound)?;

            cur_point = {
                let borrow = cur_point.borrow();
                Rc::clone(&borrow.get_conected_point(cur_dir)?)
            };

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
                || cur_point.borrow().con_type(cur_dir.anti_clockwise())
                    == TMeshConnectionType::Point
            {
                return Ok(false);
            }
        }
    }

    /// Casts a ray from `p` in the direction `dir` for `num` intersections, returning a vector containing the knot
    /// intervals of each intersection. When an edge condition is encountered before `num` intersections have been
    /// crossed, the returned vector contains the edge knot interval once, after which it is padded with `0.0`.
    /// All vectors returned from this function will have a length `num`.
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if a T-mesh is found on the edge of a face, making it non-rectangular (malformed mesh).
    ///
    /// - `TMeshControlPointNotFound` if an edge condition is found inside the mesh or
    ///     if edge condition points are not connected to each other (malformed mesh).
    ///
    /// - `Ok(vec<f64>)` if the ray was successfully cast, returns the knot intervals traversed.
    ///  
    /// # Borrows
    /// Immutably borrows `p` and any points connected to `p` in the direction `dir`, including points which go around any
    /// faces created by T-juctions in the direction `dir`, for `num` perpandicular intersections.
    pub fn cast_ray(
        p: Rc<RefCell<TMeshControlPoint<P>>>,
        dir: TMeshDirection,
        num: usize,
    ) -> Result<Vec<f64>> {
        let mut knot_intervals = Vec::with_capacity(num);
        let mut cur_point = Rc::clone(&p);

        // Some flags for special cases.
        //
        // If an edge condition is found, only the first "intersection" at the edge contion is recorded,
        // and all further deltas are 0, though according to [Sederberg et al. 2003] they do not matter.
        let mut edge_condition_found = false;

        'intersection_loop: while knot_intervals.len() < num {
            let con_type = cur_point.borrow().con_type(dir);
            let i = knot_intervals.len();
            knot_intervals.push(0.0);

            match con_type {
                // If dir is a T-junction, navigate around the face to the other side,
                // counting the knot intervals in the direction dir
                TMeshConnectionType::Tjunction => {
                    // Stores the distance traversed away from the ray
                    let mut ray_distance: f64;
                    (cur_point, ray_distance) = {
                        let borrow = cur_point.borrow();

                        // The possibility that TMeshControlPointNotFound is returned from navigate_until_con would normaly be no
                        // cuase for error, since the other direction may be tried. However, because cur_point is a T junction in
                        // the direction dir, it must be a point connection in dir.anti_clockwise(), otherwise the mesh is malformed.
                        borrow.navigate_until_con(dir.anti_clockwise(), dir)?
                    };

                    // Travrese with counting until a connection in the clockwise connection is found.
                    // Because all faces must be rectangular, this is guaranteed to be the first "ray intersection".
                    let traversal_result = cur_point
                        .borrow()
                        .navigate_until_con(dir, dir.clockwise())?;
                    cur_point = traversal_result.0;
                    // Set the latest pushed value to the intersection length
                    knot_intervals[i] += traversal_result.1;

                    // If a T-junction is encountered, it is (Figure 9 cases aside) guaranteed that on the other side of the face there
                    // is no point which perfectly aligns with the initial point. In this case, a special algorithm must be used to
                    // traverse across the mesh until such a point is found or the requisite number of intersections are reached.
                    // Example below (All distances are in parametric space and represented by physical space between "+", which are points):
                    // <+>---\+/----------------------------------+
                    //  |     |                                   |
                    //  |    [+]-----<+>--+---+-----+--<+>---<+>--+
                    //  |     |       |   |   |     |   |     |   |
                    //  |     |       |   |   |    <+>-<+>    |   |
                    //  |     |       |   |   |     |   |     |   |
                    //  |     |      [+]-(+)-<+>    |  /+\    |   |
                    //  |     |       |       |     |   |    <+>-<+>
                    //  |     |       |      <+>---<+>  |     |   |
                    // {+}~~~~|~~~~~~/+\~~~~~~|~~~~~|~~~|~~~~~|~~|+|
                    //  |     +-------+       |     |   |     |   |
                    //  |     |       |       +----/+\-/+\----+---+
                    //  |     |       |       |                   |
                    //  +-----+-------+-------+-------------------+
                    //  0     1       2       3     4   5     6   7     <-- Intersection numbers, used in comments
                    //
                    // {+} is point from which the ray is "cast"
                    // <+> are points that need to be visited by the algorithm
                    // [+] are the points where if normal ray casting is resumed,
                    //      an incorrect knot vector will be produced.
                    // (+) is a point whose knot interval will be accumulated but not recorded for
                    // |+| is the point at which "normal" ray casting continues (may or may not exist, and
                    //      must not have a T-junction to the right).
                    // /+\ are points which, while closer to the ray in a paramtric sense,
                    //      are not directly accessed for the reasons described in the next paragraph
                    // \+/ is the locatioin of cur_point
                    //  ~  is the "ray"
                    //
                    // In any case, the path taken shall not cross the ray. It can be guaranteed that any edge
                    // the ray pierces will be accessable by this algorithm due to the rectangular nature of the T-mesh.
                    // Lets say that there exists a virtical edge which the ray pierces. That edge must be connected on
                    // either edge to horrizontal edges. At the corners, there will be control points. Thus, two of
                    // the control points must be above the ray. Furthermore, to preserve the rectangular nature of
                    // each face, those control points must be connected to two other edges, meaning that at least
                    // one edge from that control point will be pointing up or left, connecting to another edge.
                    // This means that as long as the algorithm used to traverse the mesh stays as close to the ray as possible,
                    // without crossing it, (that is, always stays on a face which is intersected by the ray), there is no
                    // danger of missing an intersection and producing an incorrect knot vector.
                    //
                    // The above code is not included in the loop below because of certain guarantees that can be made about the
                    // geometry of the mesh which cannot be made for the rest of the mesh.
                    'face_traversal: loop {
                        // It is possible that we are traversing along the edge of the mesh, in this case, the below navigate_until_con is
                        // going to navigate until the corner of the mesh, and return an error that it encountered an unexpected
                        // edge condition. This is not actually an error, so it needs to be checked before traversal. In the event that this occurs,
                        // normal ray casting is resumed, since all edge conditions in a mesh have the same weight. Do not push another knot interval,
                        // because the edge arm of the parent match statement will take care of it
                        if cur_point.borrow().con_type(dir) == TMeshConnectionType::Edge {
                            break 'face_traversal;
                        }

                        // Traverse down to the lowest point on this edge which is not a T-junction and has not yet crossed the ray.
                        'ray_approaching: loop {
                            let traversal_result = cur_point
                                .borrow()
                                .navigate_until_con(dir.clockwise(), dir)?;

                            // Subtract distance as we approach the ray (temp var because the result might be
                            // over the ray, in which case we discard it).
                            let new_ray_distance = ray_distance - traversal_result.1;

                            // Found a point where normal ray traversal will continue
                            if new_ray_distance.so_small() {
                                break 'face_traversal;

                            // The detected point crosses the ray, so cur_point is the closest point to the ray with a
                            // connection in the dir direction.
                            } else if new_ray_distance < 0.0 {
                                break 'ray_approaching;
                            }

                            // Move cur_point
                            cur_point = traversal_result.0;
                            // Synchronize distance
                            ray_distance = new_ray_distance;
                        }

                        // It is possble that the above loop exited without modifying cur_point, as is the case for the face marked by
                        // the fourth and fifth intersections above. In this case, cur_point must be navigated up to the corner of the face.
                        if cur_point.borrow().con_type(dir) == TMeshConnectionType::Tjunction {
                            let traversal_result = cur_point
                                .borrow()
                                .navigate_until_con(dir.anti_clockwise(), dir)?;

                            // Move cur_point.
                            cur_point = traversal_result.0;
                            // Add distance, since we are traversing away from the ray.
                            ray_distance += traversal_result.1;
                        }

                        // Traverse accross the "top" of the face, to the other corner
                        let traversal_result = cur_point
                            .borrow()
                            .navigate_until_con(dir, dir.clockwise())?;

                        // Record the traversal distance as a knot interval (guaranteed to be correct because all faces are rectangular)
                        knot_intervals.push(traversal_result.1);
                        // Move cur_point
                        cur_point = traversal_result.0;
                    }
                }

                TMeshConnectionType::Point => {
                    // Store knot interval
                    knot_intervals[i] += cur_point.borrow().get_con_knot(dir).expect(
                        "All point connections and edge conditions must have a knot interval",
                    );

                    // Traverse to the next point
                    cur_point = {
                        let borrow = cur_point.borrow();
                        Rc::clone(
                            &borrow
                                .get_conected_point(dir)
                                .expect("Point connections must have connected points"),
                        )
                    };
                }

                TMeshConnectionType::Edge => {
                    // Edge contition already found, and pushing a zero happens before the match statement, so just continue.
                    if edge_condition_found {
                        continue;
                    }

                    // Store knot interval
                    knot_intervals[i] += cur_point.borrow().get_con_knot(dir).expect(
                        "All point connections and edge conditions must have a knot interval",
                    );

                    // Flag to store zeros for remaining deltas
                    edge_condition_found = true;
                }
            };
        }
        return Ok(knot_intervals);
    }
}

impl<P> TMesh<P>
where
    P: PartialEq,
{
    /// Finds the first point that was added to a T-mesh with a specific cartesian coordinate
    pub fn find(&self, p: P) -> Result<Rc<RefCell<TMeshControlPoint<P>>>> {
        Ok(Rc::clone(
            self.control_points()
                .iter()
                .find(|x| *x.borrow().point() == p)
                .ok_or(Error::TMeshControlPointNotFound)?,
        ))
    }
}

impl<P> TMesh<P>
where
    P: ControlPoint<f64>,
{
    pub fn try_local_knot_insertion(
        &mut self,
        p: Rc<RefCell<TMeshControlPoint<P>>>,
        dir: TMeshDirection,
        knot_ratio: f64,
    ) -> Result<()> {
        match p.borrow().con_type(dir) {
            TMeshConnectionType::Edge => return Err(Error::TMeshControlPointNotFound),
            TMeshConnectionType::Tjunction => return Err(Error::TMeshConnectionNotFound),
            _ => {}
        };

        if knot_ratio < 0.0 || knot_ratio > 1.0 {
            return Err(Error::TMeshInvalidKnotRatio);
        }

        // Rule 3 of T-splines, [Sederberg et al. 2003], states that all (The paper does not specify existing or otherwise,
        // I am assuming that they may or may not exist, however, the connection from the inner two points must not be
        // a T-junction) perpandicular and in-line knot vectors of length 5 centered on the axis
        // of insertion and a distance of at most two knots from the point to be inserted must be equal. See Figure 10 in
        // [Sederberg et al. 2003] for details.
        let mut center_points: Vec<Rc<RefCell<TMeshControlPoint<P>>>> = Vec::with_capacity(4);

        // An example insertion for reference
        //
        //   --<+>--{+}--[+]---+--<+>--
        //      0    1    ~    2   3   <- center_points and knot_vectors indicies
        // {+} is p
        // [+] is the new control point to be inserted
        // <+> may or may not exist (can only insert if they do exist)
        center_points.push({
            let borrow = p.borrow();
            // Get connected point
            if let Some(con) = borrow.get(dir.flip()).as_ref() {
                // Connection exists, add control point to center_points for knot vector extraction
                if let Some(point) = con.0.as_ref() {
                    Rc::clone(point)
                } else {
                    Rc::clone(&p)
                }
            // T junction means that a knot can not be inserted, since the knot vector for this "column's" center
            // point is going to be different, see rule 2 for T-meshes in [Sederberg et al. 2003].
            // (Maybe wrong with 0 knots? figure 9)
            } else {
                return Err(Error::TMeshConnectionNotFound);
            }
        });
        center_points.push(Rc::clone(&p));
        center_points.push({
            let borrow = p.borrow();
            // Checked in the begining of the function with match
            Rc::clone(
                &borrow
                    .get_conected_point(dir)
                    .expect("Point connections must have connected points"),
            )
        });
        center_points.push({
            // Checked in the begining of the function
            let borrow = center_points[2].as_ref().borrow();

            // Connection or T-junction
            if let Some(con) = borrow.get(dir).as_ref() {
                // Point or edge condition
                if let Some(point) = con.0.as_ref() {
                    Rc::clone(point)
                } else {
                    Rc::clone(&center_points[2])
                }
            } else {
                // T junction
                return Err(Error::TMeshConnectionNotFound);
            }
        });

        // Store the first knot vector to compare it to the rest. If any do not match, return an error
        let knot_vec_compare: KnotVec = {
            let point_knots = TMesh::get_point_knot_vectors(Rc::clone(&center_points[0]))?;

            // Depending on the direction of insertion, the S or T knot vectors are needed.
            match dir {
                TMeshDirection::LEFT | TMeshDirection::RIGHT => point_knots.1,
                TMeshDirection::DOWN | TMeshDirection::UP => point_knots.0,
            }
        };
        // Generate knot vector for each point and compare
        for point in center_points[1..].iter() {
            // Get knot vectors in both directions for the point
            let point_knots = TMesh::get_point_knot_vectors(Rc::clone(point))?;

            // Depending on the direction of insertion, the S or T knot vectors are needed.
            let cur_kv = match dir {
                TMeshDirection::LEFT | TMeshDirection::RIGHT => point_knots.1,
                TMeshDirection::DOWN | TMeshDirection::UP => point_knots.0,
            };

            if cur_kv != knot_vec_compare {
                return Err(Error::TMeshKnotVectorsNotEqual);
            }
        }

        // Get d1 - d6. See Figure 10 in [Sederberg et al. 2003].
        let mut d: Vec<f64> = Vec::with_capacity(6);
        // d1
        d.push(
            center_points[0]
                .borrow()
                .get_con_knot(dir.flip())
                .ok_or(Error::TMeshConnectionNotFound)?,
        );
        // d2
        d.push(
            center_points[1]
                .borrow()
                .get_con_knot(dir.flip())
                .ok_or(Error::TMeshConnectionNotFound)?,
        );
        // d3
        d.push(
            center_points[1]
                .borrow()
                .get_con_knot(dir)
                .ok_or(Error::TMeshConnectionNotFound)?
                * knot_ratio,
        );
        // d4
        d.push(
            center_points[2]
                .borrow()
                .get_con_knot(dir.flip())
                .ok_or(Error::TMeshConnectionNotFound)?
                * (1.0 - knot_ratio),
        );
        // d5
        d.push(
            center_points[2]
                .borrow()
                .get_con_knot(dir)
                .ok_or(Error::TMeshConnectionNotFound)?,
        );
        // d6
        d.push(
            center_points[3]
                .borrow()
                .get_con_knot(dir)
                .ok_or(Error::TMeshConnectionNotFound)?,
        );

        // Equations 5, 6, and 7 from [Sederberg et al. 2003].
        let p2_prime = ((center_points[0].borrow().point().clone() * d[3])
            + (center_points[1].borrow().point().clone().to_vec() * (d[0] + d[1] + d[2])))
            / (d[0] + d[1] + d[2] + d[3]);

        let p4_prime = ((center_points[4].borrow().point().clone() * d[2])
            + (center_points[3].borrow().point().clone().to_vec() * (d[3] + d[4] + d[5])))
            / (d[2] + d[3] + d[4] + d[5]);

        center_points[1].borrow_mut().set_point(p2_prime);
        center_points[2].borrow_mut().set_point(p4_prime);

        let p3_prime = ((center_points[1].borrow().point().clone() * (d[3] + d[4]))
            + (center_points[3].borrow().point().clone().to_vec() * (d[1] + d[2])))
            / (d[1] + d[2] + d[3] + d[4]);

        self.add_control_point(p3_prime, Rc::clone(&p), dir, knot_ratio)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let point_con = &point_borrow.get_conected_point(dir).map_err(|e| (0, e))?;
        let point_equal = Rc::ptr_eq(point_con, &other);
        point_equal
            .then(|| 0)
            .ok_or((0, Error::TMeshExistingConnection))?;

        // Check that other is connected to point
        let other_borrow = other.borrow();
        let other_con = &other_borrow
            .get_conected_point(dir.flip())
            .map_err(|e| (1, e))?;
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
                .is_some_and(|c| c.0.is_none() && (c.1 - 1.0).so_small()),
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

            (borrow
                .get_con_knot(TMeshDirection::DOWN)
                .expect("Connection should exist")
                - 1.0)
                .so_small()
        };
        assert!(
            inferred_con_interval,
            "Inferred connection knot interval is incorrect"
        );
    }

    /// Tests to make sure that a mesh with the following shape is correctly formed and connected. Knot intervals may be arbitrary,
    /// however, cartesian points must be located on a 0.5 spaced grid with a 0 z-coordinate. Thus, the center point is
    /// located at `(0.5, 0.5, 0)` and so on.
    /// ```
    ///    |  |  |
    ///  --+--+--+--
    ///    |  |  |
    ///  --+--+--+--
    ///    |  |  |
    ///  --+--+--+--
    ///    |  |  |
    /// ```
    fn test_t_mesh_plus_mesh(mesh: &TMesh<Point3>) {
        let middle = mesh.find(Point3::from((0.5, 0.5, 0.0))).unwrap();

        // Test connections in the four directions
        let up_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((0.5, 1.0, 0.0))).unwrap()),
            TMeshDirection::UP,
        );
        assert!(up_con.is_ok(), "Middle is not correctly connected to UP");

        let right_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((1.0, 0.5, 0.0))).unwrap()),
            TMeshDirection::RIGHT,
        );
        assert!(
            right_con.is_ok(),
            "Middle is not correctly connected to RIGHT"
        );

        let down_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((0.5, 0.0, 0.0))).unwrap()),
            TMeshDirection::DOWN,
        );
        assert!(
            down_con.is_ok(),
            "Middle is not correctly connected to DOWN"
        );

        let left_con = test_points_are_connected(
            Rc::clone(&middle),
            Rc::clone(&mesh.find(Point3::from((0.0, 0.5, 0.0))).unwrap()),
            TMeshDirection::LEFT,
        );
        assert!(
            left_con.is_ok(),
            "Middle is not correctly connected to LEFT"
        );
    }

    /// Constructs a T-mesh, testing that inserting a new control point with two inferred connections
    /// produces the correct result. Utilizes the `add_control_point` function for point insertion.
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
    /// `[+]` is the inserted control point, which is tested. The control point is inserted on the `DOWN` connection of
    /// `<+>`, and the connections marked `~` are inferred connections which should exist after `[+]` is inserted.
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

        test_t_mesh_plus_mesh(&mesh);
    }

    /// Constructs a T-mesh, testing that inserting a new control point with two inferred connections
    /// produces the correct result. Utilizes the `try_add_absolute_point` function for point insertion.
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
    /// `[+]` is the inserted control point, which is tested. The control point is inserted on the `DOWN` connection of
    /// `<+>`, and the connections marked `~` are inferred connections which should exist after `[+]` is inserted.
    #[test]
    fn test_t_mesh_try_add_absolute_point_mesh_construction() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);

        // Insert virtical aspect of the plus
        mesh.try_add_absolute_point(Point3::from((0.0, 0.5, 0.0)), (0.0, 0.5))
            .expect("Legal point insertion");
        mesh.try_add_absolute_point(Point3::from((1.0, 0.5, 0.0)), (1.0, 0.5))
            .expect("Legal point insertion");

        // Insert horrizontal aspect of the plus
        mesh.try_add_absolute_point(Point3::from((0.5, 0.0, 0.0)), (0.5, 0.0))
            .expect("Legal point insertion");
        mesh.try_add_absolute_point(Point3::from((0.5, 1.0, 0.0)), (0.5, 1.0))
            .expect("Legal point insertion");

        // Insert center point of the plus
        mesh.try_add_absolute_point(Point3::from((0.5, 0.5, 0.0)), (0.5, 0.5))
            .expect("Legal point insertion");

        test_t_mesh_plus_mesh(&mesh);
    }

    /// Constructs the following T-mesh, testing that inserting a new control point using
    /// `try_add_absolute_point` function produces a point with the correct knot intervals.
    ///
    /// ```
    ///    |       |
    ///  --+-------+--
    ///    |       |
    ///  --+-+-----+--
    ///    | |     |
    /// ```
    #[test]
    fn test_t_mesh_try_add_absolute_point_knot_intervals() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);
        mesh.try_add_absolute_point(Point3::from((0.2, 0.0, 0.0)), (0.2, 0.0))
            .expect("Legal point insertion");

        // Insert a point asymetrically into a mesh to test if knot interval calculations work
        let knot_interval_check = mesh
            .find(Point3::from((0.2, 0.0, 0.0)))
            .expect("Control point previously inserted into mesh");

        // Left connectioin should be connected to (0, 0, 0), with interval 0.2
        assert_eq!(
            knot_interval_check
                .borrow()
                .get_con_knot(TMeshDirection::LEFT)
                .expect("Known existing connection"),
            0.2,
            "Knot inverval on LEFT does not match expectation"
        );

        // Right connectioin should be connected to (1, 0, 0), with interval 0.8
        assert_eq!(
            knot_interval_check
                .borrow()
                .get_con_knot(TMeshDirection::RIGHT)
                .expect("Known existing connection"),
            0.8,
            "Knot inverval on RIGHT does not match expectation"
        );
    }

    /// Constructs a T-mesh, testing that inserting a new control point using
    /// `try_add_absolute_point` function produces errors when attempting to insert an unconnected point,
    /// an existing point, and an out-of-bound point.
    ///
    /// ```            
    ///             {+}
    ///    |   |     
    ///  --+---+--
    ///    |[+]|
    ///  -<+>--+--
    ///    |   |
    /// ```
    /// <+> is the duplicate point
    /// [+] is the unconnected pont
    /// {+} is the out-of-bounds point
    #[test]
    fn test_t_mesh_try_add_absolute_point_invalid_insertion() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);

        // Test errors on inserting a point into the center of a face (unconnected point)
        assert!(mesh
            .try_add_absolute_point(Point3::from((0.5, 0.5, 0.0)), (0.5, 0.5))
            .is_err_and(|e| { e == Error::TMeshConnectionNotFound }),
            "Expected Error TMeshConnectionNotFound when attempting to insert a point in a location with no intersecting mesh edges.");

        // Test errors on zero intervals (duplicate point)
        assert!(mesh
            .try_add_absolute_point(Point3::from((0.0, 0.0, 0.0)), (0.0, 0.0))
            .is_err_and(|e| { e == Error::TMeshExistingControlPoint }),
            "Expected Error TMeshExistingControlPoint when attempting to insert a point in a location where a control point already exists.");

        // Test errrors on out-of-bounds insertions.
        assert!(mesh
            .try_add_absolute_point(Point3::from((2.0, 2.0, 0.0)), (2.0, 2.0))
            .is_err_and(|e| { e == Error::TMeshConnectionInvalidKnotInterval }),
            "Expected Error TMeshConnectionInvalidKnotInterval when attempting to insert a point outside the parametric domain of the mesh.");
    }

    /// Constructs the following T-mesh, testing that navigating from the origin to a connection in the
    /// right direction functions as expected.
    ///
    /// ```
    ///    |      |
    ///  --+------+--
    ///    |      |
    ///  --+      |
    ///    |      |
    ///  --+------+--
    ///    |      |
    /// ```
    /// <+> is the duplicate point
    /// [+] is the unconnected pont
    /// {+} is the out-of-bounds point
    #[test]
    fn test_t_mesh_navigate_until_con_existing_con() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);
        let origin = mesh
            .find(Point3::from((0.0, 0.0, 0.0)))
            .expect("Point exists in T-mesh");

        // Add control point for navigation
        mesh.add_control_point(
            Point3::from((0.0, 0.5, 0.0)),
            Rc::clone(&origin),
            TMeshDirection::UP,
            0.5,
        )
        .expect("Valid addition of control point.");

        // Navigates to the top left point
        let navigation_result = origin
            .borrow()
            .navigate_until_con(TMeshDirection::UP, TMeshDirection::RIGHT);

        assert!(
            navigation_result.is_ok(),
            "Error navigating until existing connecton"
        );
        assert_eq!(
            navigation_result.as_ref().unwrap().0.borrow().point,
            Point3::from((0.0, 1.0, 0.0)),
            "Navigation returned incorrect point"
        );
        assert_eq!(
            navigation_result.as_ref().unwrap().1,
            1.0,
            "Navigation knot interval incorrect"
        );
    }

    /// Constructs the following T-mesh, testing that navigating from the origin to a connection in the
    /// left direction returns an error.
    ///
    /// ```
    ///    |      |
    ///  --+------+--
    ///    |      |
    ///  --+      |
    ///    |      |
    ///  --+------+--
    ///    |      |
    /// ```
    /// <+> is the duplicate point
    /// [+] is the unconnected pont
    /// {+} is the out-of-bounds point
    #[test]
    fn test_t_mesh_navigate_until_con_no_existing_con() {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 1.0);
        let origin = mesh
            .find(Point3::from((0.0, 0.0, 0.0)))
            .expect("Point exists in T-mesh");

        // Add control point for navigation
        mesh.add_control_point(
            Point3::from((0.0, 0.5, 0.0)),
            Rc::clone(&origin),
            TMeshDirection::UP,
            0.5,
        )
        .expect("Valid addition of control point.");

        // Navigate until error
        let navigation_result = origin
            .borrow()
            .navigate_until_con(TMeshDirection::UP, TMeshDirection::LEFT);

        assert!(
            navigation_result.is_err(),
            "Navigation to non-existant connection succeeded (Should have failed)"
        );
        assert_eq!(
            navigation_result.as_ref().err(),
            Some(&Error::TMeshControlPointNotFound),
            "Expected TMeshControlPointNotFound, got {:?}",
            navigation_result.as_ref().err()
        );
    }

    /// Constructs the following T-mesh, with the knot coordinates specified on the left and bottom. All edge condition
    ///  intervals have a knot interval of 2.5.
    ///
    /// ```
    ///  1.0   +-----+-----------------------------------+
    ///        |     |                                   |
    ///  0.9   |     +-------+---+---+-----+---+-----+---+
    ///        |     |       |   |   |     |   |     |   |
    ///  0.8   |     |       |   |   |     +---+     |   |
    ///        |     |       |   |   |     |   |     |   |
    ///  0.7   |     |       +---+---+     |   +     |   |
    ///  0.6   |     |       |       |     |   |     +---+
    ///  0.5   |     |       |       +-----+   |     |   |
    ///  0.4   +     |       +       |     |   |     |   +
    ///  0.3   |     +-------+       |     |   |     |   |
    ///  0.2   |     |       |       +-----+---+-----+---+
    ///        |     |       |       |                   |
    ///  0.0   +-----+-------+-------+-------------------+
    ///       0.0   0.2     0.3 0.4 0.5  0.6  0.7   0.9 1.0
    /// ```
    fn construct_ray_casting_example_mesh() -> TMesh<Point3> {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 0.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 0.0)),
        ];

        let mut mesh = TMesh::new(points, 2.5);

        // Absolute knot coordinatess of the points from the mesh above. They are ordered such that the
        // edges in the above image will be constructed without conflict, and so that points are only
        // inserted on existing edges.
        let knot_pairs = Vec::from([
            (0.0, 0.4),
            (0.2, 1.0),
            (1.0, 0.9),
            (1.0, 0.6),
            (1.0, 0.2),
            (0.5, 0.0),
            (0.3, 0.0),
            (0.2, 0.0),
            (0.2, 0.3),
            (0.2, 0.9),
            (0.3, 0.9),
            (0.4, 0.9),
            (0.5, 0.9),
            (0.6, 0.9),
            (0.7, 0.9),
            (0.9, 0.9),
            (0.3, 0.7),
            (0.3, 0.4),
            (0.3, 0.3),
            (0.5, 0.7),
            (0.5, 0.5),
            (0.5, 0.2),
            (0.4, 0.7),
            (0.6, 0.2),
            (0.7, 0.2),
            (0.9, 0.2),
            (0.6, 0.5),
            (0.6, 0.8),
            (0.7, 0.7),
            (0.7, 0.8),
            (0.9, 0.6),
            (1.0, 0.4),
        ]);

        // Construct mesh
        for knot_pair in knot_pairs {
            mesh.try_add_absolute_point(Point3::from((knot_pair.0, knot_pair.1, 0.0)), knot_pair)
                .expect(
                    format!(
                        "Valid addition of control point ({}, {}).",
                        knot_pair.0, knot_pair.1
                    )
                    .as_str(),
                );
        }

        mesh
    }

    /// Tests if the face intersection algorithm in cast_ray functions as expected. Does not test if the
    /// edge detection or connection traversal aspects of the algorithm function as expected. Uses the mesh
    /// constructed by construct_ray_casting_example_mesh to test cast_ray, by casting a ray from the point
    /// located at (0.0, 0.4) in parametric space in the direction RIGHT.
    #[test]
    fn test_t_mesh_ray_casting_face_intersection() {
        // Construct mesh
        let mesh = construct_ray_casting_example_mesh();

        // Select the initial point
        let start = mesh
            .find(Point3::from((0.0, 0.4, 0.0)))
            .expect("Known existing point in mesh");

        // Cast ray
        let intersections = TMesh::cast_ray(Rc::clone(&start), TMeshDirection::RIGHT, 9);

        assert!(
            intersections.is_ok(),
            "Ray casting produces unexpectd error"
        );
        let intersections = intersections.unwrap();

        // Because 9 intersections are requested in the cast_ray function call, the returned vector must be of length 9
        assert_eq!(
            intersections.len(),
            9,
            "The incorrect number of intervals was returned"
        );

        // Check values in the returned vector.
        assert!(
            intersections
                .iter()
                .zip(Vec::from([0.2, 0.1, 0.2, 0.1, 0.1, 0.2, 0.1, 2.5, 0.0]))
                .all(|p| (p.0 - p.1).so_small()),
            "Recorded knot intervals differ form expectation"
        );
    }
}

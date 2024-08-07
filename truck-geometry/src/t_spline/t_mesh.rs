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
            bezier_domains: RefCell::new(None),
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
    /// - `TMeshConnectionNotFound` if `con` has no connection on `connection_side`.
    ///
    /// - `TMeshControlPointNotFound` if `con` is an edge condition on `connction_side`.
    ///
    /// - `TMeshForeignControlPoint` if `con` is not a control point in the T-mesh.
    ///
    /// - `TMeshConnectionInvalidKnotInterval` if the connection between `con`
    ///     and the point in the direction `connection_side`, `con_side`, does not have the same
    ///     knot interval in both directions (`con` -> `con_side` != `con` <- `con_side`).
    ///     This should never happen.
    ///
    /// - `Ok(())` if the control point was successfully added
    ///
    /// # Borrows
    /// Mutably borrows `con` and the point located in the direction `connection_side`, and potentially borrows all
    /// points that are a part of the faces on either side of the edge that connects `p` and the point located in
    /// the direction `connection_side`.
    ///
    /// Mutably borrows `self.bezier_domains`
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
            return Err(Error::TMeshForeignControlPoint);
        }

        // Get the point currently connected to the connection point. Returns the
        // requisit errors in the case that the connection is not of type Point.
        let other_point = {
            let borrow = con.borrow();
            Rc::clone(&borrow.try_get_conected_point(connection_side)?)
        };

        // Edge weights for p are set to 0.0, however, the final step will overwrite this
        // if a different edge weight was specified in the T-mesh constructor
        let p = Rc::new(RefCell::new(TMeshControlPoint::new(p, 0.0)));

        let knot_interval = con
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
        con.borrow_mut()
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
            Rc::clone(&con),
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
        if con.borrow().con_type(connection_side.clockwise()) == TMeshConnectionType::Edge {
            let edge_weight = con
                .borrow()
                .get_con_knot(connection_side.clockwise())
                .expect("Edges must have a weight");

            p.borrow_mut()
                .set_edge_con_weight(connection_side.clockwise(), edge_weight)
                .expect("New points have edge conditions as default connection type.");
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

        if con.borrow().con_type(connection_side.anti_clockwise()) == TMeshConnectionType::Edge {
            let edge_weight = con
                .borrow()
                .get_con_knot(connection_side.anti_clockwise())
                .expect("Edges must have a weight");

            p.borrow_mut()
                .set_edge_con_weight(connection_side.anti_clockwise(), edge_weight)
                .expect("New points have edge conditions as default connection type.");
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
        self.bezier_domains.replace(None);
        Ok(())
    }

    /// Attemps to add a control point to the mesh given the cartesian point `p` and the absolute knot coordinates `knot_coords`
    /// in the form `(s, t)`. In order for insertion to succeed, there must either be an S or T edge located at the parametric
    /// point `knot_coords` in the mesh `self`. Note that zero knot insertions will return an error, as the side on which to
    /// insert the zero knot is ambiguous.
    ///
    /// # Returns
    /// - `TMeshOutOfBoundsInsertion` if a control point is being inserted with either knot coordinate out of the range `[0.0, 1.0]`.
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
        // Make sure desred knot coordinates are within mesh bounds
        if knot_coords.0 < 0.0 || knot_coords.0 > 1.0 || knot_coords.1 < 0.0 || knot_coords.1 > 1.0
        {
            return Err(Error::TMeshOutOfBoundsInsertion);
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
    /// where `S_vector` is the horizontal knot vector and `T_vector` is the virtical knot vector. Both knot vectors shall
    /// be of length 5
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if a T-junction is unexpectedly found (non-rectangular face)
    ///
    /// - `TMeshControlPointNotFound` if an edge conditon is unexpectedly found (internal edge condition)
    ///
    /// - `Ok((KnotVeec, KnotVec))` if knot vectors are successfully generated
    ///
    /// # Borrows
    /// Immutably borrows `p` and all points connected to `p` in all directions for a distance of two knot intervals.
    /// In the case that `p` is not connected to a point in a direction, but instead a T-junction, any points
    /// that are a part of the face which `p` is a part of and the next face in that direction may be borrowed,
    /// with no guarantees as to which or how many.
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
    /// While this function is capable of inserting points with zero knot intervals in every (legaal)
    /// case, there are no guarantees as to how points will be connected with a zero knot interval
    /// regarding implicit connections (Cross-face connections).
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
            let accumulation: f64;

            (cur_point, accumulation) = cur_point
                .borrow()
                .navigate_until_con(cur_dir, cur_dir.anti_clockwise())?;

            cur_dir = cur_dir.anti_clockwise();

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
                Rc::clone(&borrow.try_get_conected_point(cur_dir)?)
            };

            // Ic found
            if (ic_knot_measurment - ic_knot_accumulation).so_small() {
                let connection_res = TMeshControlPoint::connect(
                    Rc::clone(&p),
                    Rc::clone(&cur_point),
                    cur_dir.clockwise(),
                    ic_knot_interval,
                );

                // If an existing connection is found, it is possible that the next point over
                // will be a zero knot interval, in which case the connection should go to that point.
                // Any other error should be sent up and if the connection is successful the same thing should happen.
                match connection_res {
                    Ok(()) => return Ok(true),
                    Err(Error::TMeshExistingConnection) => {}
                    Err(e) => return Err(e),
                };

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

                        if knot_intervals.len() == num {
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
                        Rc::clone(&borrow.get_conected_point(dir))
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
    /// Attempts to insert a new control point between two existing control points. In order to do so, the knot vectors
    /// perpandicular to the connection for two control points in both directions (including the control points which
    /// define the edge) must be equal. See the figure below for an example.
    ///
    /// ```
    ///     t1   t2        t3   t4
    ///     +----+---------+----+
    ///     |    |         |    |
    ///     +----+---------+----+
    ///     |    |         |    |
    ///  --<+>--{+}--[+]--{+}--<+>--
    ///     |    |         |    |
    ///     +----+---------+----+
    ///     |    |         |    |
    ///     +----+----+----+----+
    /// ```
    ///
    /// - `<+>` are points which may or may not exist, but if they do not exist, must be replaced with an edge
    ///     condition. A T-junction will cause an error.
    /// - `{+}` are points which must exist, one of which will be `p`.
    /// - `[+]` is the point to be inserted.
    /// - `t1 - t5` are the knot vectors perpandicular to the axis of insertion
    ///
    /// In the above example, the virtical knot vectors defined by the paramtric spacing between all the points `+` with no
    /// wrapping must be equal (tollerance is used, so exact floating point equality is not nescessary).
    ///
    /// # Returns
    ///
    /// - `TMeshControlPointNotFound` if `p` is an edge condition in the direction `dir`.
    /// 
    /// - `TMeshConnectionNotFound` if a T-junction is encountered instead of a control point or an edge condition
    ///     along the axis of insertion (Rule 3 \[Sederberg et al. 2003\]).
    /// 
    /// - `TMeshInvalidKnotRatio` if `knot_ratio` is not in [0.0, 1.0]. 
    /// 
    /// - `TMeshMalformedMesh` if a knot vector was unable to be constructed for any point.
    ///
    /// - `TMeshKnotVectorsNotEqual` if the knot vectors perpandicular to `dir` are not all equal (Rule 3 \[Sederberg et al. 2003\]).
    /// 
    /// - `TMeshForeignControlPoint` if `p` is not a control point in the T-mesh.
    /// 
    /// - `TMeshConnectionInvalidKnotInterval` if the connection between `p` and the point in the direction `dir` does 
    ///     not have the same knot interval in both directions.
    /// 
    /// - `Ok(())` if the control point was successfully added.
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
        let mut center_points: Vec<Option<Rc<RefCell<TMeshControlPoint<P>>>>> =
            Vec::with_capacity(4);

        // An example insertion for reference
        //
        //   --<+>--{+}--[+]---+--<+>--
        //      0    1    ~    2   3   <- center_points and knot_vectors indicies
        // {+} is p
        // [+] is the new control point to be inserted
        // <+> may or may not exist (can only insert if they are replaced with edge conditions)
        center_points.push({
            match p.borrow().con_type(dir.flip()) {
                // Retrieve connected point
                TMeshConnectionType::Point => {
                    Some(Rc::clone(&p.borrow().get_conected_point(dir.flip())))
                }
                TMeshConnectionType::Edge => None,
                TMeshConnectionType::Tjunction => {
                    return Err(Error::TMeshConnectionNotFound);
                }
            }
        });
        center_points.push(Some(Rc::clone(&p)));
        center_points.push({
            let borrow = p.borrow();
            // Checked in the begining of the function with match
            Some(Rc::clone(&borrow.get_conected_point(dir)))
        });
        center_points.push({
            let con_point = Rc::clone(&center_points[2]
                .as_ref()
                .expect("center_points[2] is a required control point"));
                
            let borrow = con_point.borrow();

            match borrow.con_type(dir.flip()).clone() {
                // Retrieve connected point
                TMeshConnectionType::Point => {
                    Some(Rc::clone(&borrow.get_conected_point(dir)))
                }
                TMeshConnectionType::Edge => None,
                TMeshConnectionType::Tjunction => {
                    return Err(Error::TMeshConnectionNotFound);
                }
            }
        });

        // Store the first knot vector to compare it to the rest. If any do not match, return an error
        let knot_vec_compare: KnotVec = {
            let point_knots = TMesh::get_point_knot_vectors(Rc::clone(
                &center_points[1].as_ref().expect("center_points[1] is a required point"),
            ))?;

            // Depending on the direction of insertion, the S or T knot vectors are needed.
            if dir.horizontal() {
                point_knots.1
            } else {
                point_knots.0
            }
        };
        // Generate knot vector for each point and compare (Compares center_points[1] to itself,
        // but I am not sure of the best way to get around this. Ask me in a couple of weeks once I've
        // learned how to use this language).
        for opt in center_points[1..].iter() {
            // Get knot vectors in both directions for the point
            let point_knots = if let Some(point) = opt {
                TMesh::get_point_knot_vectors(Rc::clone(point)).map_err(|_| Error::TMeshMalformedMesh)?
            } else {
                continue;
            };

            // Depending on the direction of insertion, the S or T knot vectors are needed.
            let cur_kv = if dir.horizontal() {
                point_knots.1
            } else {
                point_knots.0
            };

            // Compare knot vectors using so_small because knot vector construction uses
            // knot intervals which are prone to small errors.
            if cur_kv
                .iter()
                .zip(knot_vec_compare.iter())
                .all(|t| (t.0 - t.1).so_small())
            {
                return Err(Error::TMeshKnotVectorsNotEqual);
            }
        }

        // Get d1 - d6. See Figure 10 in [Sederberg et al. 2003].
        let mut d: Vec<f64> = Vec::with_capacity(6);
        // d1 and d2
        for opt in center_points[0..2].iter() {
            d.push(if let Some(point) = opt.as_ref() {
                point
                    .borrow()
                    .get_con_knot(dir.flip())
                    .ok_or(Error::TMeshConnectionNotFound)?
            } else {
                0.0
            });
        }
        // d3
        d.push(
            center_points[1]
                .as_ref()
                .expect("center_points[1] is a requird point")
                .borrow()
                .get_con_knot(dir)
                .ok_or(Error::TMeshConnectionNotFound)?
                * knot_ratio,
        );
        // d4
        d.push(d.last().expect("Vector should not be empty") * ((1.0 / knot_ratio) - 1.0));
        // d5 and d6
        for opt in center_points[3..5].iter() {
            d.push(if let Some(point) = opt.as_ref() {
                point
                    .borrow()
                    .get_con_knot(dir)
                    .ok_or(Error::TMeshConnectionNotFound)?
            } else {
                0.0
            });
        }

        let cartesian_points: Vec<P> = center_points
            .iter()
            .map(|opt| {
                if let Some(p) = opt {
                    p.borrow().point().clone()
                } else {
                    P::origin()
                }
            })
            .collect();

        // Equations 5, 6, and 7 from [Sederberg et al. 2003].
        let p2_prime = ((cartesian_points[0].clone() * d[3])
            + (cartesian_points[1].clone().to_vec() * (d[0] + d[1] + d[2])))
            / (d[0] + d[1] + d[2] + d[3]);

        let p4_prime = ((cartesian_points[4].clone() * d[2])
            + (cartesian_points[3].clone().to_vec() * (d[3] + d[4] + d[5])))
            / (d[2] + d[3] + d[4] + d[5]);

        let p3_prime = ((cartesian_points[1].clone() * (d[3] + d[4]))
            + (cartesian_points[3].clone().to_vec() * (d[1] + d[2])))
            / (d[1] + d[2] + d[3] + d[4]);

        center_points[1]
            .as_ref()
            .expect("center_points[1] is a required point")
            .borrow_mut()
            .set_point(p2_prime);

        center_points[2]
            .as_ref()
            .expect("center_points[2] is a required point")
            .borrow_mut()
            .set_point(p4_prime);

        self.add_control_point(p3_prime, Rc::clone(&p), dir, knot_ratio)?;

        Ok(())
    }

    pub fn try_absolute_local_knot_insertion(&mut self, knot_coords: (f64, f64)) -> Result<()> {
        // Make sure desred knot coordinates are within msh bounds
        if knot_coords.0 < 0.0 || knot_coords.0 > 1.0 || knot_coords.1 < 0.0 || knot_coords.1 > 1.0
        {
            return Err(Error::TMeshOutOfBoundsInsertion);
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
                return self.try_local_knot_insertion(
                    Rc::clone(&s_axis_stradle_points[0]),
                    TMeshDirection::UP,
                    (knot_coords.1 - point_t_coord) / con_knot,
                );
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
                return self.try_local_knot_insertion(
                    Rc::clone(&t_axis_stradle_points[0]),
                    TMeshDirection::RIGHT,
                    (knot_coords.0 - point_s_coord) / con_knot,
                );
            }
            _ => {
                // Multiple S-edges are found where the point intersects (Should never happen)
                return Err(Error::TMeshMalformedMesh);
            }
        };
    }

    fn try_bezier_domains(&self) -> Result<TMesh<P>> {
        let mut mesh = self.clone();

        // Bezier domains are constructed by direction, not by point. The alternative can lead to situations
        // where local knot insertion fails not because of the geometry of the original mesh, but because
        // the inserted bezier knots have resulted in a mesh which is "grid-locked", at which point local
        // knot insertion fails at multiple positions.

        for dir in [
            TMeshDirection::UP,
            TMeshDirection::DOWN,
            TMeshDirection::RIGHT,
            TMeshDirection::LEFT,
        ] {
            // New T-junctions are created when bezier domains are created, so use self's control points while modifying mesh's.
            // Indecies stay the same, since new control points are pushed onto the cotnrol_points vector in mesh
            for (index, original_mesh_cont_p) in self.control_points.iter().enumerate() {
                if original_mesh_cont_p.borrow().con_type(dir) == TMeshConnectionType::Tjunction {
                    let coresponding_point = Rc::clone(&mesh.control_points[index]);
                    let mut knot_intervals =
                        TMesh::cast_ray(Rc::clone(&coresponding_point), dir, 2)
                            .map_err(|_| Error::TMeshMalformedMesh)?;

                    // Convert relative deltas in knot_invervals into absolute deltas (point to point distances to absolute distances)
                    knot_intervals[1] += knot_intervals[0];

                    for interval in knot_intervals {
                        let coords = dir.mutate_knot_coordinates(
                            coresponding_point.borrow().get_knot_coordinates(),
                            interval,
                        );
                        mesh.try_absolute_local_knot_insertion(coords)?;
                    }
                }
            }
        }

        Ok(mesh)
    }

    /// Returns the cartesian point corresponding to the parametric coordinates for `self`. Usually the
    /// parametric coordinates are constrained from 0 to 1 for both `s` and `t` as this is the domain of
    /// the T-mesh in parametric space. However, parameters are not checked or forcefully constrained,
    /// as there is a domain of continuity outside the usual parameter range. This domain, however, is not
    /// guaranteed, and should be accessed at your own risk.
    ///
    /// # Returns
    /// - `TMeshConnectionNotFound` if `self` contains a non-rectangular grid, in which case generating knot vectors will fail.
    ///
    /// - `TMeshControlPointNotFound` if `self` contains an edge condition inside of its mesh.
    ///
    /// - `Ok(P)` if the calculation succeeded. A `P` will be returned which is the T-mesh transformation
    ///     of `(s, t)` into cartesian space.
    ///
    /// # Borrows
    /// Immutably borrows every control point in `self`.
    ///
    /// Mutably borrows `self.bezier_domains`.
    pub fn subs(&self, s: f64, t: f64) -> Result<P> {
        // Generate bezier domains and knot vectors if stale
        if self.bezier_domains.borrow().is_none() {
            self.bezier_domains
                .replace(Some(Box::new(self.try_bezier_domains()?)));
            self.bezier_domains
                .borrow_mut()
                .as_mut()
                .expect("Bezier domains should have succesfully generated or an error produced")
                .generate_knot_vectors()?;
        }

        // S is horizontal
        // T is virtical

        // Currently the basis functions for each point are being generated every time `subs` is called
        // TODO: Move basis functions out of `subs` into `self`
        let mut basis_evaluations = Vec::new();
        for (i, _) in self.control_points.iter().enumerate() {
            // Though using the existing b-spline struct in TRUCK would be nice, unfourtunatly I haven't been able to get it to work, since it is not exactly a b-spline that is being calculated, but a specific b-spline basis function, which I haven't been able to extract from the b-spline struct. In order to produce the correct basis function, a significant ammount of brut force was used. First, the Cox-de Boor recursion formula from https://pages.mtu.edu/~shene/COURSES/cs3621/NOTES/spline/B-spline/bspline-basis.html was used with a little lua script to create a series of functions which could be plugged into desmos. Then, they were flattened into one function of considerable length. To see those functions, see https://www.desmos.com/calculator/on6vmapdcb. Then, the equation was simplified and split into four piecewise functions which corresponded to each of the four domains of the original function, where each function contributes one segment of the resulting basis function and does not overlap with any other function. To see those functions, see https://www.desmos.com/calculator/qikhwjjzxy. These final four piecewise functins are used to create the basis functions below.
            let basis_function = |u: f64, a: Vec<f64>| -> f64 {
                // If u is out of bounds, return 0.0 quickly before checking which range it falls into.
                if u < a[0] || a[4] <= u {
                    return 0.0;
                }

                if u < a[1] {
                    let mut numerator = u - a[0];
                    numerator *= numerator * numerator; // Cubed

                    let mut denominator = a[3] - a[0];
                    denominator *= a[2] - a[0];
                    denominator *= a[1] - a[0];
                    return numerator / denominator;
                } else if u < a[2] {
                    let scalar = 1.0 / (a[2] - a[1]);
                    // Knot vector indices for each of the fractions in N_{2}(u) from the second desmos link.
                    // Each tuple is a term containing a tuple of indices for the numerator and denominator respectively.
                    let sum = Vec::from([
                        ((0, 0, 2), (3, 0, 2, 0)),
                        ((0, 1, 3), (3, 0, 3, 1)),
                        ((1, 1, 4), (4, 1, 3, 1)),
                    ])
                    .iter()
                    .fold(0.0, |sum, (num, den)| {
                        sum + (((u - a[num.0]) * (u - a[num.1]) * (a[num.2] - u))
                            / ((a[den.0] - a[den.1]) * (a[den.2] - a[den.3])))
                    });

                    return scalar * sum;
                } else if u < a[3] {
                    let scalar = 1.0 / (a[3] - a[2]);
                    // Knot vector indices for each of the fractions in N_{2}(u) from the second desmos link.
                    // Each tuple is a term containing a tuple of indices for the numerator and denominator respectively.
                    let sum = Vec::from([
                        ((0, 3, 3), (3, 0, 3, 1)),
                        ((1, 4, 3), (4, 1, 3, 1)),
                        ((2, 4, 4), (4, 1, 4, 2)),
                    ])
                    .iter()
                    .fold(0.0, |sum, (num, den)| {
                        sum + (((u - a[num.0]) * (a[num.1] - u) * (a[num.2] - u))
                            / ((a[den.0] - a[den.1]) * (a[den.2] - a[den.3])))
                    });

                    return scalar * sum;
                } else if u < a[4] {
                    let mut numerator = a[4] - u;
                    numerator *= numerator * numerator; // Cubed

                    let mut denominator = a[4] - a[1];
                    denominator *= a[4] - a[2];
                    denominator *= a[4] - a[3];
                    return numerator / denominator;
                }
                // Control flow will never reach here, however, rather than having an else statement at the bottom which
                // is either the out-of-bounds case (most likely) or the final range (not explicit enough for my taste)
                // I would rather just leave this here for you <3
                0.0
            };

            basis_evaluations.push({
                let borrow = self.bezier_domains.borrow();

                let knot_vectors = &borrow
                    .as_ref()
                    .expect("Program should not reach basis evaluation if bezier generation failed")
                    .knot_vectors
                    .as_ref()
                    .expect("Knot vectors should have successfully generated or an error returned")
                    [i];

                let s_eval = basis_function(s, knot_vectors.0.to_vec());
                let t_eval = basis_function(t, knot_vectors.1.to_vec());
                s_eval * t_eval
            });
            // basis_functions.push(move |s_param: f64, t_param: f64| -> P {
            //     // Input point is located outside of influence domain of basis function.
            //     if s_param < knots.0[0]
            //         || s_param > knots.0[4]
            //         || t_param < knots.1[0]
            //         || t_param > knots.1[4]
            //     {
            //         return point * 0.0;
            //     }
            //     // Using De Boor's algorithm is faster than brute force, and we
            //     // don't need the individual polynomial coefficients
            //     // From: https://pages.mtu.edu/~shene/COURSES/cs3621/NOTES/spline/B-spline/de-Boor.html
            //     const P: usize = 3;
            //     //      u = s or t
            //     //
            //     // The contribution of the current point is a tensor product of the two B splines.
            //     // Compute each individually and then multiply
            //
            //     // First B spline (horizontal)
            //     for knot_v in [&knots.0, &knots.1] {
            //         // k from the website
            //         let floor_idx = knot_v
            //             .floor(s_param)
            //             .expect("Bounds were previously checked");
            //         let h: usize;
            //         // Mutliplicity is s on the website
            //         let multiplicity: usize;
            //
            //         // "If u lies in (u_k, u_k+1), h = p"
            //         if knot_v[floor_idx] != s_param {
            //             multiplicity = 0;
            //             h = P;
            //
            //         // "If u = u_k, h = p - s"
            //         } else {
            //             multiplicity = knot_v.multiplicity(floor_idx);
            //             h = P - multiplicity;
            //         }
            //
            //         for r in 1..=h {
            //             for i in (floor_idx - P + r)..=(floor_idx - multiplicity) {}
            //         }
            //     }
            //
            //     point
            // })
        }

        let numerator = basis_evaluations.iter().zip(self.bezier_domains
                    .borrow()
                    .as_ref()
                    .expect(
                        "Control flow should not reach basis multiplication if bezier domain generation failed",
                    )
                    .control_points()[..self.control_points().len()]
                    .iter()
                    .map(|c| c.borrow().point().clone()),
            )
            .fold(P::origin(), |sum, (b, p)| sum + p.to_vec() * *b);

        let denominator: f64 = basis_evaluations.iter().sum();
        Ok(numerator / denominator)
    }
}

impl<P> fmt::Display for TMesh<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // If only Hash Maps could use f64....
        let mut s_levels: Vec<(f64, Vec<Rc<RefCell<TMeshControlPoint<P>>>>)> = Vec::new();
        let mut t_levels: Vec<(f64, Vec<Rc<RefCell<TMeshControlPoint<P>>>>)> = Vec::new();

        let sort_f64 = |a: &f64, b: &f64| -> std::cmp::Ordering {
            if (a - b).so_small() {
                return std::cmp::Ordering::Equal;
            } else if a > b {
                return std::cmp::Ordering::Greater;
            }
            return std::cmp::Ordering::Less;
        };

        for point in self.control_points.iter() {
            let coords = point.borrow().get_knot_coordinates();

            if let Some(s_level) = s_levels
                .iter_mut()
                .find(|c| sort_f64(&c.0, &coords.0) == std::cmp::Ordering::Equal)
            {
                let point_vec: &mut Vec<Rc<RefCell<TMeshControlPoint<P>>>> = s_level.1.as_mut();
                point_vec.push(Rc::clone(point));
            } else {
                s_levels.push((coords.0, Vec::new()));
                s_levels
                    .last_mut()
                    .expect("Pushed element on previous line.")
                    .1
                    .push(Rc::clone(point));
            }

            if let Some(t_level) = t_levels
                .iter_mut()
                .find(|c| sort_f64(&c.0, &coords.1) == std::cmp::Ordering::Equal)
            {
                let point_vec: &mut Vec<Rc<RefCell<TMeshControlPoint<P>>>> = t_level.1.as_mut();
                point_vec.push(Rc::clone(point));
            } else {
                t_levels.push((coords.1, Vec::new()));
                t_levels
                    .last_mut()
                    .expect("Pushed element on previous line.")
                    .1
                    .push(Rc::clone(point));
            }
        }

        s_levels.sort_unstable_by(|a, b| sort_f64(&a.0, &b.0));
        t_levels.sort_unstable_by(|a, b| sort_f64(&a.0, &b.0));

        t_levels = t_levels.into_iter().rev().collect();

        let mut virtical_cons: Vec<bool> = vec![false; s_levels.len()];
        for (i, (s_level, _)) in s_levels.iter().enumerate() {
            if let Some(point) = t_levels[0]
                .1
                .iter()
                .find(|p| p.borrow().get_knot_coordinates().0 == *s_level)
            {
                virtical_cons[i] =
                    point.borrow().con_type(TMeshDirection::UP) != TMeshConnectionType::Tjunction;
            }
        }
        write!(f, "       ")?;
        let mut line = String::new();
        for con in virtical_cons.iter() {
            if *con {
                line.push_str("|   ");
            } else {
                line.push_str("    ");
            }
        }
        write!(f, "{}\n", line)?;

        // let line_len = 2 * s_levels.len();
        for t_level in t_levels {
            let mut line = String::new();
            let mut has_left_edge = false;
            let mut has_right_edge = false;

            for (i, (s_level, _)) in s_levels.iter().enumerate() {
                if let Some(point) = t_level
                    .1
                    .iter()
                    .find(|p| p.borrow().get_knot_coordinates().0 == *s_level)
                {
                    if point.borrow().con_type(TMeshDirection::LEFT) == TMeshConnectionType::Edge {
                        line.push_str("--");
                        has_left_edge = true;
                    }

                    line.push('+');
                    virtical_cons[i] = point.borrow().con_type(TMeshDirection::DOWN)
                        != TMeshConnectionType::Tjunction;
                    line.push_str(match point.borrow().con_type(TMeshDirection::RIGHT) {
                        TMeshConnectionType::Edge => "--",
                        TMeshConnectionType::Point => {
                            has_right_edge = true;
                            "---"
                        }
                        TMeshConnectionType::Tjunction => {
                            has_right_edge = false;
                            "   "
                        }
                    });
                } else if virtical_cons[i] {
                    line.push_str("|   ");
                } else if has_right_edge {
                    line.push_str("----");
                } else {
                    line.push_str("    ");
                }
            }

            write!(f, "{:.2} ", t_level.0)?;
            if !has_left_edge {
                write!(f, "  ")?;
            }
            write!(f, "{}\n", line)?;

            write!(f, "       ")?;
            let mut line = String::new();
            for con in virtical_cons.iter() {
                if *con {
                    line.push_str("|   ");
                } else {
                    line.push_str("    ");
                }
            }
            write!(f, "{}\n", line)?;
        }

        let mut s_demarcations = (
            format!("{:.2}", s_levels[0].0),
            format!("{:.2}", s_levels[1].0),
        );
        for (i, s_level) in s_levels[2..].iter().enumerate() {
            if i % 2 == 0 {
                s_demarcations
                    .0
                    .push(if virtical_cons[i + 1] { '|' } else { ' ' });
                s_demarcations
                    .0
                    .push_str(format!("   {:.2}", s_level.0).as_str());
            } else {
                s_demarcations
                    .1
                    .push_str(format!("    {:.2}", s_level.0).as_str());
            }
        }

        if *virtical_cons
            .last()
            .expect("All T-meshes have at least 2 S-levels")
            && s_levels.len() % 2 == 0
        {
            s_demarcations.0.push('|');
        }

        write!(f, "       ")?;
        write!(f, "{}\n", s_demarcations.0)?;
        write!(f, "           ")?;
        write!(f, "{}\n", s_demarcations.1)?;
        Ok(())
    }
}

impl<P> Clone for TMesh<P>
where
    P: Clone,
{
    fn clone(&self) -> TMesh<P> {
        // Vector containing new point objects which have the same positions as the points in the original mesh
        let mut points_copy = Vec::new();
        // Vector containing the connections for each point with the corresponding index in points_copy.
        // Each sub-vector will be 4 elements long, and each element of the sub-vector will be None if the
        // connection is a T-junction, Some((None, f64)) for an Edge condition, and Some((Some(index), f64))
        // for a Point connection, where index is the index of the connected point in self.control_points,
        // and thus points_copy by extension.
        let mut point_connections: Vec<Vec<Option<(Option<usize>, f64)>>> = Vec::new();

        // Copy all the points into points_copy and all connections into point_connections
        for point in self.control_points.iter() {
            // Clone the cartesian point
            let cart_point = {
                let borrow = point.borrow();
                borrow.point().clone()
            };
            // Push a new control point corresponding to the control point in self.control_points to points_copy
            // The edge interval is 1.0, however, this can be any value, since establishing connections will
            // overwrite this with the correct value.
            points_copy.push(Rc::new(RefCell::new(TMeshControlPoint::new(
                cart_point, 1.0,
            ))));

            // Push a new set of connections
            point_connections.push(Vec::new());
            // Retrieve the previously pushed set of connections for ease of use.
            let last = point_connections
                .last_mut()
                .expect("Previously pushed item");

            // TMeshDirection::iter() produces the same order of directions every time, so all connection
            // sub-vectors in point_connections will be ordered in the same way, and will be read the same
            // way during connection establishment.
            for dir in TMeshDirection::iter() {
                match point.borrow().con_type(dir) {
                    // Some((None, f64))
                    TMeshConnectionType::Edge => last.push(Some((
                        None,
                        point
                            .borrow()
                            .get_con_knot(dir)
                            .expect("Edge connection types must have a knot interval."),
                    ))),
                    // Some((Some(Index), f64))
                    TMeshConnectionType::Point => {
                        let connected_point = point.borrow().get_conected_point(dir);

                        last.push(Some(
                        (Some(
                            self.control_points
                                .iter()
                                .position(|p| std::ptr::eq(p.as_ref(), connected_point.as_ref())).expect("All connected points must be stored in tmesh control_points vector"),
                        ), point.borrow().get_con_knot(dir).expect("Point connection types must have a knot interval.")),
                    ))
                    }
                    // None
                    TMeshConnectionType::Tjunction => {
                        last.push(None);
                    }
                };
            }
        }

        // Establish connections
        'points_loop: for (point_index, connections) in point_connections.iter().enumerate() {
            // Zip direction with corresponding connections to index the direction for modification
            'connections_loop: for (connection, dir) in
                connections.iter().zip(TMeshDirection::iter())
            {
                if let Some(con) = connection {
                    // Point connection
                    if let Some(con_index) = con.0 {
                        // Connections has already been established. Connect will also add the connection to points_copy[con_index],
                        // so when points_copy[con_index] is reached by 'points_loop, the connection will already exist, so we skip it.
                        if points_copy[point_index].borrow().con_type(dir)
                            == TMeshConnectionType::Point
                        {
                            continue 'connections_loop;
                        }

                        // Remove existing edge conditions from both points to be connected.
                        {
                            points_copy[point_index]
                                .borrow_mut()
                                .remove_connection(dir)
                                .expect("Connections are only modified once.");
                            points_copy[con_index]
                                .borrow_mut()
                                .remove_connection(dir.flip())
                                .expect("Connections are only modified once.");
                        }

                        // Connect points to each other
                        TMeshControlPoint::connect(
                            Rc::clone(&points_copy[point_index]),
                            Rc::clone(&points_copy[con_index]),
                            dir,
                            con.1,
                        )
                        .expect("Control points have no connections between each other.")
                    // Edge condition
                    } else {
                        points_copy[point_index]
                            .borrow_mut()
                            .set_edge_con_weight(dir, con.1)
                            .expect(
                                "Unmodified control points have edge conditions in all directions.",
                            );
                    }
                // T-junction
                } else {
                    points_copy[point_index]
                        .borrow_mut()
                        .remove_connection(dir)
                        .expect(
                            "Unmodified control points have edge conditions in all directions.",
                        );
                }
            }
        }

        // Set absolute knot coordinates
        for (i, p) in self.control_points().iter().enumerate() {
            points_copy[i].borrow_mut().knot_coordinates = p.borrow().get_knot_coordinates();
        }

        TMesh {
            control_points: points_copy,
            knot_vectors: None,
            bezier_domains: RefCell::new(None),
        }
    }
}

impl<T> Drop for TMesh<T> {
    fn drop(&mut self) {
        // Destroy all connections in the mesh so that the only remaining reference to all the points is in
        // self.control_points to prevent leaks
        for p in self.control_points.iter() {
            for dir in TMeshDirection::iter() {
                let _ = p.borrow_mut().remove_connection(dir);
            }
        }
    }
}

impl<T> TMesh<T>
where
    T: Debug + Clone,
{
    pub fn print_debug_info(&self) {
        for point in self.control_points() {
            let cart = {
                let borrow = point.borrow();
                (*borrow.point()).clone()
            };
            let knot_vectors = TMesh::get_point_knot_vectors(Rc::clone(point))
                .expect("Mesh should not be malformd");
            println!("{:?}", cart);
            println!("\tS: {:?}", knot_vectors.0);
            println!("\tT: {:?}", knot_vectors.1);
            println!("");
        }
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
        let point_con = &point_borrow
            .try_get_conected_point(dir)
            .map_err(|e| (0, e))?;
        let point_equal = Rc::ptr_eq(point_con, &other);
        point_equal
            .then(|| 0)
            .ok_or((0, Error::TMeshExistingConnection))?;

        // Check that other is connected to point
        let other_borrow = other.borrow();
        let other_con = &other_borrow
            .try_get_conected_point(dir.flip())
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
            .is_err_and(|e| { e == Error::TMeshOutOfBoundsInsertion }),
            "Expected Error TMeshOutOfBoundsInsertion when attempting to insert a point outside the parametric domain of the mesh.");
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

    /// Constructs the following (unsolvable) T-mesh, with the knot coordinates specified on the left and bottom. All edge condition
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

    /// Tests if the face intersection algorithm in cast_ray functions as expected, including testing if the
    /// point-edge detection, but not connection traversal, aspect of the algorithm function as expected. Uses the mesh
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

    /// Tests if the face intersection algorithm in cast_ray functions as expected. Does not test if the
    /// edge detection or connection traversal aspects of the algorithm function as expected, however,
    /// it does test if the T-junction traversal algorithm terminates when expected. Uses the mesh
    /// constructed by construct_ray_casting_example_mesh to test cast_ray, by casting a ray from the point
    /// located at (0.0, 0.4) in parametric space in the direction RIGHT.
    #[test]
    fn test_t_mesh_ray_casting_face_intersection_incomplete_cast() {
        // Construct mesh
        let mesh = construct_ray_casting_example_mesh();

        // Select the initial point
        let start = mesh
            .find(Point3::from((0.0, 0.4, 0.0)))
            .expect("Known existing point in mesh");

        // Cast ray
        let intersections = TMesh::cast_ray(Rc::clone(&start), TMeshDirection::RIGHT, 5);

        assert!(
            intersections.is_ok(),
            "Ray casting produces unexpectd error"
        );
        let intersections = intersections.unwrap();

        // Because 9 intersections are requested in the cast_ray function call, the returned vector must be of length 9
        assert_eq!(
            intersections.len(),
            5,
            "The incorrect number of intervals was returned"
        );

        // Check values in the returned vector.
        assert!(
            intersections
                .iter()
                .zip(Vec::from([0.2, 0.1, 0.2, 0.1, 0.1]))
                .all(|p| (p.0 - p.1).so_small()),
            "Recorded knot intervals differ form expectation"
        );
    }

    /// Tests if the face intersection algorithm in cast_ray functions as expected, including testing if the
    /// T-junction edge detection and connection traversal aspects of the algorithm function as expected. Uses the mesh
    /// constructed by construct_ray_casting_example_mesh to test cast_ray, by casting a ray from the point
    /// located at (0.0, 0.4) in parametric space in the direction RIGHT.
    #[test]
    fn test_t_mesh_ray_casting_non_point_edge_condition() {
        // Construct mesh
        let mesh = construct_ray_casting_example_mesh();

        // Select the initial point
        let start = mesh
            .find(Point3::from((0.3, 0.7, 0.0)))
            .expect("Known existing point in mesh");

        // Cast ray
        let intersections = TMesh::cast_ray(Rc::clone(&start), TMeshDirection::RIGHT, 8);

        assert!(
            intersections.is_ok(),
            "Ray casting produces unexpectd error"
        );
        let intersections = intersections.unwrap();
        println!("{:?}", intersections);
        // Because 9 intersections are requested in the cast_ray function call, the returned vector must be of length 9
        assert_eq!(
            intersections.len(),
            8,
            "The incorrect number of intervals was returned"
        );

        // Check values in the returned vector.
        assert!(
            intersections
                .iter()
                .zip(Vec::from([0.1, 0.1, 0.1, 0.1, 0.2, 0.1, 2.5, 0.0]))
                .all(|p| (p.0 - p.1).so_small()),
            "Recorded knot intervals differ form expectation"
        );
    }

    /// Clones the mesh produced by `construct_ray_casting_example_mesh` and then compares it to a second,
    /// uncloned mesh from `construct_ray_casting_example_mesh`.
    #[test]
    fn test_t_mesh_clone() {
        let tmesh_test = construct_ray_casting_example_mesh().clone();
        let tmesh_comp = construct_ray_casting_example_mesh();

        // Test number of control points
        assert!(
            tmesh_test.control_points().len() == tmesh_comp.control_points().len(),
            "Number of control points in mesh is not the same as original mesh"
        );

        // Test cartesian points
        assert!(
            tmesh_test
                .control_points()
                .iter()
                .zip(tmesh_comp.control_points().iter())
                .all(|p| { p.0.borrow().point() == p.1.borrow().point() }),
            "Control points of cloned mesh are not the same as original mesh"
        );

        // Test parametric points
        assert!(
            tmesh_test
                .control_points()
                .iter()
                .zip(tmesh_comp.control_points().iter())
                .all(|p| {
                    p.0.borrow().get_knot_coordinates() == p.1.borrow().get_knot_coordinates()
                }),
            "Parametric coordinates of cloned mesh are not the same as original mesh"
        );

        // Test connections
        assert!(tmesh_test
            .control_points()
            .iter()
            .zip(tmesh_comp.control_points().iter())
            .all(|p| {
                // Test all directions of every point in the meshes
                for dir in TMeshDirection::iter() {
                    // Compare connection types
                    if p.0.borrow().con_type(dir) != p.1.borrow().con_type(dir) {
                        return false;
                    }

                    // Based on the conenction type, compare connected objects
                    match p.0.borrow().con_type(dir) {
                        TMeshConnectionType::Edge => {
                            // Compare knot intervals
                            if p.0.borrow().get_con_knot(dir) != p.1.borrow().get_con_knot(dir) {
                                return false;
                            }
                        }
                        TMeshConnectionType::Point => {
                            // Compare knot intervals
                            if p.0.borrow().get_con_knot(dir) != p.1.borrow().get_con_knot(dir) {
                                return false;
                            }

                            // Get connection object from both meshes
                            let test_borrow = p.0.borrow();
                            let test_con = test_borrow
                                .get(dir)
                                .as_ref()
                                .expect("Point con type must have a connection");
                            let comp_borrow = p.1.borrow();
                            let comp_con = comp_borrow
                                .get(dir)
                                .as_ref()
                                .expect("Point con type must have a connection");

                            // Compare connected points
                            if test_con
                                .0
                                .as_ref()
                                .expect("Point con type must have a point connected")
                                .borrow()
                                .point()
                                != comp_con
                                    .0
                                    .as_ref()
                                    .expect("Point con type must have a point connected")
                                    .borrow()
                                    .point()
                            {
                                return false;
                            }
                        }
                        TMeshConnectionType::Tjunction => {}
                    }
                }

                true
            }))
    }

    #[test]
    fn test_t_mesh_subs() {
        const C: usize = 100;
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 1.0)),
            Point3::from((1.0, 1.0, 2.0)),
            Point3::from((0.0, 1.0, 1.0)),
        ];

        // Tmesh is now a surface where all point on the surface are of the form (f(x), g(y), f(x) + g(y))
        // approximates x + y = z with medial x and y values
        let mut mesh = TMesh::new(points, 1.0);

        for s in 0..C {
            let s = s as f64 / C as f64;
            for t in 0..C {
                let t = t as f64 / C as f64;
                let p = mesh
                    .subs(s, t)
                    .expect("Solvable T-mesh with s and t within bounds");

                assert!(
                    ((p.x + p.y) - p.z).so_small(),
                    "Returned subs value does not match expectation."
                );
            }
        }
    }
}

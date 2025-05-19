use super::*;
use crate::errors::Error;

impl<P> Tnurcc<P>
where
    P: Debug,
{
    /// Creates a new `Tnurcc` instance. `points` is a vector containing the control points in the mesh, and `faces`
    /// describes the connections of the mesh. `faces` must described every face in the mesh, as no `faces` will be
    /// infered by the constructor. Each face in `faces` contains 4 edges. Each edge is described by a tuple containing
    /// an initial point index and a vector containing the other point indicies and knot intervals on the edge.
    /// It is important to note that because there is no sense of orientation in the T-NURCC, the points in edges, and
    /// the edges themselves must be arranged in the correct order prior to instantiating the `Tnurcc` relative to each
    /// other. All point indicies refer to the indecies of the points in the `points` parameter.
    ///
    /// Put together, this means that in an edge, the initial point index must be either the clockwise first corner or
    /// anti-clockwise first corner (Recommended to use anti-clockwise for face culling reasons). That is to say, for the
    /// "top" edge, the "right" corner should be used as the initial point index. Then, the connected points vector should
    /// contain the indicies of the points in order, sweeping across the "top" edge and their knot intervals. For a visual
    /// explenation, see the figure below.
    ///
    /// ```
    ///     0    6   8  9
    ///   4 +----+---+--+
    ///     |           |
    ///     |           |
    ///   2 |           +
    ///     |           |
    ///   0 +--+---+----+
    ///     0  5   7    9
    /// ```
    /// In the above figure, the numbers represent the cartesian coordinate of the points, while the number of `-`
    /// (minus) or `|` (virtical pipe) characters between them represents the knot interval. In this case, `points`
    /// might be the vector:
    ///
    /// `[(0, 0), (5, 0), (7, 0), (9, 0), (0, 3), (9, 2), (0, 4), (6, 4), (8, 4), (9, 4)]`
    ///
    /// The `points` vector does not need to have a specific order, however, the ordering of the elements in `points`
    /// will change the indicies in `faces`. The above example is also only one face, whereas most T-NURCCs will have
    /// multiple faces. Each point should be included exactly once in the `points` vector regardless of how many faces
    /// it participates in. Then, the edges for the face, if made anti-clockwise, could be:
    ///
    /// `[(0, [(1, 2.0), (2, 3.0), (3, 4.0)]), (3, [(5, 1.0), (9, 2.0)]), (9, [(8, 2.0), (7, 3.0), (6, 4.0)]), (6, [(0, 4.0)])]`
    ///
    /// Notice that the knot interval for points in the connections vector is the relative knot distance between the point it is
    /// tuple'd with and the point *prior* to it. The above face vector is one of four possible identical face elements, where
    /// the other three are the rotations of the edge elements in the face. The edges are also ordered in an anti-clockwise.
    ///
    /// It is mandatory that all faces have the same knot interval spanning opposing edges. In the example above, that means that the
    /// "top" and "bottom" face must have the same total knot interval, and the same goes for the "left" and "right". In short, all faces
    /// must be rectangular in knot-space (parametrically rectangular).
    ///
    /// # Returns
    ///
    /// - `TnurccNonRectangularFace` if any face is not parametrically rectangular.
    ///
    /// - `TnurccEdgeTrippleFace` if any edge lies between three faces.
    ///
    /// - `TnurccIncompleteFaceEdge` if any edge is comprised of less than 2 points.
    ///
    /// - `Ok(Tnurcc)` if the T-NURCC was succsefully created.
    ///
    /// # Panics
    pub fn try_new(points: Vec<P>, faces: Vec<[(usize, Vec<(usize, f64)>); 4]>) -> Result<Self> {
        let mut control_points = Vec::with_capacity(points.len());

        for (index, point) in points.into_iter().enumerate() {
            control_points.push(Rc::new(RefCell::new(TnurccControlPoint::new(index, point))));
        }

        let mut tnurcc_faces = Vec::new();
        let mut edges: Vec<Rc<RefCell<TnurccEdge<P>>>> = Vec::new();
        for face in faces {
            // Verify that the face has the same knot interval on opposing faces by summing interval for each side
            let dimensions: Vec<f64> = face
                .iter()
                .map(|e| e.1.iter().fold(0.0, |s, p| s + p.1))
                .collect();

            // Subtract opposing side's knot intervals
            if !(dimensions[0] - dimensions[2] + dimensions[1] - dimensions[3]).so_small() {
                return Err(Error::TnurccNonRectangularFace);
            }

            // Produce a vector containing all the point indicies in the face, in order, such that any two adjacent element
            // in the vector should be connected, and a vector containing each connection's weight.
            let (mut connections, knot_intervals) = face
                .into_iter()
                // Converet the format of the side into an array of all points in the side. Remember that sides must,
                // in addition to specifying the initial point, specify the last point in agreement with the first
                // point of the next anti-clockwise side. Thus, we can ignore the initial point, since it is contained
                // in the previous edge's connections vector.
                .map(|e| e.1)
                // Flatten the sides together into the indicies of the edge
                .flatten()
                .collect::<(Vec<_>, Vec<_>)>();

            // The last connection is between the first and last element, which is included in this by adding the
            // first control point to the end of the vector o that a window will pick it up
            connections.push(connections[0]);

            // Collect all edges described by face (This is such a painfully O(N*M) algorithm I don't
            // want to think about it but I'm currently at a loss for what else to do about it...)
            let mut existing_edges: Vec<_> = {
                let map_closure = |c: &[usize]| {
                    edges
                        .iter()
                        .find(|e| {
                            let borrow = e.borrow();
                            let origin_index = borrow.origin.borrow().index;
                            let dest_index = borrow.dest.borrow().index;

                            c.contains(&origin_index) && c.contains(&dest_index)
                        })
                        .map(|r| Rc::clone(r))
                };

                connections.windows(2).map(map_closure).collect()
            };

            let face = Rc::new(RefCell::new(TnurccFace {
                index: tnurcc_faces.len(),
                edge: None,
                corners: [const { None }; 4],
            }));
            for con_index in 0..existing_edges.len() {
                if let Some(edge) = existing_edges[con_index].as_ref() {
                    if edge.borrow().face_right.is_some() {
                        return Err(Error::TnurccEdgeTrippleFace);
                    }

                    edge.borrow_mut().face_right = Some(Rc::clone(&face));
                    if face.borrow().edge.is_none() {
                        face.borrow_mut().edge = Some(Rc::clone(&edge));
                    }

                    // Connect the current edge to the previous edge in the loop
                    if con_index > 0 {
                        let con_res = TnurccEdge::connect(
                            Rc::clone(&edge),
                            Rc::clone(
                                &existing_edges[con_index - 1]
                                    .as_ref()
                                    .expect("Previous edge should always exist"),
                            ),
                        );
                        // Map success types
                        if let Err(e) = con_res {
                            return Err(e);
                        }
                    }
                } else {
                    let from = connections[con_index];
                    let to = connections[con_index + 1];
                    let index = edges.len();
                    let edge = TnurccEdge::new(
                        index,
                        knot_intervals[con_index],
                        Rc::clone(&control_points[from]),
                        Rc::clone(&control_points[to]),
                    );

                    edge.borrow_mut().face_left = Some(Rc::clone(&face));
                    if face.borrow().edge.is_none() {
                        face.borrow_mut().edge = Some(Rc::clone(&edge));
                    }

                    if con_index > 0 {
                        let con_res = TnurccEdge::connect(
                            Rc::clone(&edge),
                            Rc::clone(
                                &existing_edges[con_index - 1]
                                    .as_ref()
                                    .expect("Previous edge should always exist"),
                            ),
                        );
                        // Map success types
                        if let Err(e) = con_res {
                            return Err(e);
                        }
                    }
                    edges.push(Rc::clone(&edge));
                    existing_edges[con_index].replace(Rc::clone(&edge));
                }
            }

            let first_edge = Rc::clone(
                existing_edges[0]
                    .as_ref()
                    .expect("All edges should exist after loop"),
            );

            let last_edge = Rc::clone(
                existing_edges
                    .last()
                    .expect("existing_edges should contain multiple edges")
                    .as_ref()
                    .expect("All edges should exist after loop"),
            );

            // Connect the first and the last edge
            let con_res = TnurccEdge::connect(Rc::clone(&first_edge), Rc::clone(&last_edge));
            // Map success types
            if let Err(e) = con_res {
                return Err(e);
            }

            tnurcc_faces.push(face);
        }
        for e in edges.iter() {
            if e.borrow().face_left.is_none() || e.borrow().face_right.is_none() {
                return Err(Error::TnurccMissingFace);
            }
        }

        // Collect all extraordinary points (points with valence )
        let extraordinary_control_points = control_points
            .iter()
            .filter(|p| p.borrow().valence != 4)
            .map(|p| Rc::clone(p))
            .collect();

        Ok(Tnurcc {
            edges,
            control_points,
            extraordinary_control_points,
            faces: tnurcc_faces,
        })
    }

    /// Creates a new `Tnurcc` instance using `try_new`, panicking if it fails. See [`Tnurcc::try_new`] for details on the constructor.
    ///
    /// # Panics
    /// Panics if construction fails.
    pub fn new(points: Vec<P>, faces: Vec<[(usize, Vec<(usize, f64)>); 4]>) -> Self {
        Tnurcc::try_new(points, faces).unwrap()
    }
}

impl<P> Tnurcc<P>
where
    P: ControlPoint<f64>,
{
    /// Performs the global subdivide algorithm required by \[Sederberg et al. 2003\] and described
    /// in \[Sederberg et al. 1998\], dubbed "refinement".
    /// 
    /// # Returns
    /// - `Ok(())` on succesfull subdivision.
    /// - `TnurccMalformedFace` if boundary vertecies for a face cannot be collected.
    /// 
    /// # Panics
    /// - If any borrow fails.
    /// - If any reference geometry does not correctly point to the object it is referencing.
    /// - If any new connections or edge splits fail.
    /// 
    /// # Borrows
    /// Mutably borrows `self.edges`, `self.control_points`, and `self.faces`, as well as all elements contained within.
    pub fn global_subdivide(&mut self) -> Result<()> {
        use TnurccConnection::*;
        let mut face_points = Vec::with_capacity(self.faces.len());
        let mut edge_points = Vec::with_capacity(self.edges.len());
        let mut edge_m_points = Vec::with_capacity(self.edges.len());
        let mut split_edge = vec![false; self.edges.len()];
        // let mut vertex_points = Vec::with_capacity(self.control_points.len());
        // Used for creation of emtpy edges whose control points are not yet known
        let dummy_point = Rc::new(RefCell::new(TnurccControlPoint::new(0, P::origin())));

        // Some wrapped functions which apply in the specific case here where edges are being
        // retrieved from control points, guaranteeing membership.
        let nth_acw_int = |e, p, n| {
            TnurccEdge::nth_acw_edge_from_point(e, p, n)
                .expect("Edge should contain point it was synthesized from")
                .borrow()
                .knot_interval
        };
        let nth_cw_int = |e, p, n| {
            TnurccEdge::nth_cw_edge_from_point(e, p, n)
                .expect("Edge should contain point it was synthesized from")
                .borrow()
                .knot_interval
        };

        // Calculate new face points
        for face in self.faces.iter() {
            let mut w_vec = Vec::with_capacity(self.faces.len());
            let mut w_points = Vec::with_capacity(self.faces.len());

            let mut cir_points = TnurccFace::get_boundry_verticies(Rc::clone(face));
            // If there are no points defining a face, that is a problem.
            if cir_points.len() == 0 {
                return Err(Error::TnurccMalformedFace);
            }
            // Copy the first 4 points to the end of the array to extend the windows of the array so that the
            // first and last two points in the array are given a window in which they are the "center" element.
            cir_points.push(Rc::clone(&cir_points[0]));
            cir_points.push(Rc::clone(&cir_points[1]));
            cir_points.push(Rc::clone(&cir_points[2]));
            cir_points.push(Rc::clone(&cir_points[3]));

            for win in cir_points.windows(5) {
                // let (pm2, pm1, p, pp1, pp2) = (win[0], win[1], win[2], win[3], win[4]);
                // Array structures as [d_{i-2, i-2}, d_{i-1, i}, d_{i, i+1}, d_{i+1, i+2}]
                let edges = win
                    .windows(2)
                    .map(|a| {
                        TnurccControlPoint::edge_from_opposing_point(
                            Rc::clone(&a[0]),
                            Rc::clone(&a[1]),
                        )
                        .expect("adjacent vertecies in a face should be connected by an edge")
                    })
                    .collect::<Vec<_>>();

                let first_sum = edges[2].borrow().knot_interval                 // d_{i+1, i}^{0}
                    + nth_acw_int(Rc::clone(&edges[2]), Rc::clone(&win[3]), 2)  // d_{i+1, i}^{2}
                    + nth_cw_int(Rc::clone(&edges[2]), Rc::clone(&win[3]), 2)   // d_{i+1, i}^{-2}
                    + edges[0].borrow().knot_interval                           // d_{i-2, i-1}^{0}
                    + nth_acw_int(Rc::clone(&edges[0]), Rc::clone(&win[0]), 2)  // d_{i-2, i-1}^{2}
                    + nth_cw_int(Rc::clone(&edges[0]), Rc::clone(&win[0]), 2); // d_{i-2, i-1}^{-2}

                let second_sum = edges[1].borrow().knot_interval                 // d_{i-1, i}^{0}
                    + nth_acw_int(Rc::clone(&edges[1]), Rc::clone(&win[1]), 2)  // d_{i-1, i}^{2}
                    + nth_cw_int(Rc::clone(&edges[1]), Rc::clone(&win[1]), 2)   // d_{i-1, i}^{-2}
                    + edges[3].borrow().knot_interval                           // d_{i+2, i+1}^{0}
                    + nth_acw_int(Rc::clone(&edges[3]), Rc::clone(&win[4]), 2)  // d_{i+2, i+1}^{2}
                    + nth_cw_int(Rc::clone(&edges[3]), Rc::clone(&win[4]), 2); // d_{i+2, i+1}^{-2}

                let w = first_sum * second_sum;
                let w_p = win[2].borrow().point * w;
                w_vec.push(w);
                w_points.push(w_p);
            }

            let face_point: P = w_points
                .into_iter()
                .fold(P::origin(), |sum, p| sum + p.to_vec())
                / w_vec.iter().sum();
            face_points.push(face_point);
        }

        // Compute the location of the new point which splits every edge in mesh
        // (Equation 13  in \[Sederberg et al. 1998\])
        for edge in self.edges.iter() {
            // Equivalen to F_{ij} in Equation 13 of \[Sederberg et al. 1998\]
            let f_od = face_points[edge
                .borrow()
                .face_left
                .as_ref()
                .expect("All edges should have faces on both sides")
                .borrow()
                .index];
            // Equivalen to F_{ji} in Equation 13 of \[Sederberg et al. 1998\]
            let f_do = face_points[edge
                .borrow()
                .face_right
                .as_ref()
                .expect("All edges should have faces on both sides")
                .borrow()
                .index];

            // Denominator of equation 14 in \[Sederberg et al. 1998\]
            let a_denom: f64 = (0..4)
                .map(|n| {
                    edge.borrow()
                        .get_connection(TnurccConnection::from_usize(n))
                        .borrow()
                        .knot_interval
                })
                .sum::<f64>()
                * 2.0;

            // Equation 14 in \[Sederberg et al. 1998\] for alpha_{ij}
            // TODO: Check that the TnurccConnection parity is correct (L/R)
            let a_od = {
                if a_denom.so_small() {
                    0.0
                } else {
                    [LeftAcw, LeftCw]
                        .iter()
                        .map(|c| edge.borrow().get_connection(*c).borrow().knot_interval)
                        .sum::<f64>()
                        / a_denom
                }
            };
            // Equation 14 in \[Sederberg et al. 1998\] for alpha_{ji}
            // TODO: Check that the TnurccConnection parity is correct (L/R)
            let a_do = {
                if a_denom.so_small() {
                    0.0
                } else {
                    [RightAcw, RightCw]
                        .iter()
                        .map(|c| edge.borrow().get_connection(*c).borrow().knot_interval)
                        .sum::<f64>()
                        / a_denom
                }
            };
            // Equation 15 in \[Sederberg et al. 1998\]
            let m: P = {
                let num_dest_sum = edge.borrow().knot_interval
                    + nth_acw_int(Rc::clone(&edge), Rc::clone(&edge.borrow().origin), 2)
                    + nth_cw_int(Rc::clone(&edge), Rc::clone(&edge.borrow().origin), 2);
                let num_origin_sum = edge.borrow().knot_interval
                    + nth_acw_int(Rc::clone(&edge), Rc::clone(&edge.borrow().dest), 2)
                    + nth_cw_int(Rc::clone(&edge), Rc::clone(&edge.borrow().dest), 2);
                let m_denom = num_dest_sum + num_origin_sum;

                let origin = edge.borrow().origin.borrow().point.clone();
                let dest = edge.borrow().dest.borrow().point.clone();

                // If block not in the paper, but seems nescessary
                if m_denom.so_small() {
                    (origin + dest.to_vec()) * 0.5
                } else {
                    (origin * num_dest_sum + (dest * num_origin_sum).to_vec()) / m_denom
                }
            };
            edge_m_points.push(m.clone());

            let e = m * (1.0 - a_do - a_od) + (f_od * a_od).to_vec() + (f_do * a_do).to_vec();
            edge_points.push(e);
        }

        // Compute the new location of every vertex in the mesh
        // (Equation 16  in \[Sederberg et al. 1998\])
        for vertex in self.control_points.iter() {
            let p_naught = vertex.borrow().point.clone();
            let valence = vertex.borrow().valence as f64;

            // Get radial edges and push first again as last for last window
            let mut radial_edges = TnurccControlPoint::radial_edges(Rc::clone(vertex));
            if radial_edges.len() == 0 {
                // Probably needs its own error
                // TODO: Fix the Tnurcc errors?
                return Err(Error::TnurccMalformedFace);
            }
            radial_edges.push(Rc::clone(&radial_edges[0]));

            // Group radial edges into windows of 2. This is not strictly nesessary for the calculations
            // (in \[Sederberg et al. 1998\] they do not do this), however, it makes aquiring the radial
            // faces around the vertex much easier, as the common face between two edges can be used, and
            // then the first edge in the window will always be the "actionable" edge which is used for
            // the equations specified in \[Sederberg et al. 1998\]. The accumulator variable is a tuple
            // containing the numerator and denominator from equation 16 in \[Sederberg et al. 1998\],
            // respectively, sans the integer multiples 3 and n.
            let factional_components =
                radial_edges
                    .windows(2)
                    .fold((P::origin(), 0.0), |acc, win| {
                        let face = win[0]
                            .borrow()
                            .get_common_face(Rc::clone(&win[1]))
                            .expect("Adjacent edges should share a face.");
                        // Get the face point calculated in equation 11 in \[Sederberg et al. 1998\]
                        let f_point = face_points[face.borrow().index].clone();
                        // Equation 18 in \[Sederberg et al. 1998\]. Radial faces are in ACW order, so win[0] is the
                        // edge from which the next ACW edge is retrieved, and vice-versa
                        let f_scalar = nth_acw_int(Rc::clone(&win[0]), Rc::clone(&vertex), 1)
                            * nth_cw_int(Rc::clone(&win[1]), Rc::clone(&vertex), 1);

                        // Get the edge point calculated in equation 15 in \[Sederberg et al. 1998\]
                        let m_point = edge_points[win[0].borrow().index].clone();
                        // Equation 17 in \[Sederberg et al. 1998\]
                        let m_scalar = 0.5
                            * (nth_acw_int(Rc::clone(&win[0]), Rc::clone(&vertex), 1)
                                + nth_cw_int(Rc::clone(&win[0]), Rc::clone(&vertex), 1))
                            * (nth_acw_int(Rc::clone(&win[0]), Rc::clone(&vertex), 2)
                                + nth_cw_int(Rc::clone(&win[0]), Rc::clone(&vertex), 2));

                        (
                            acc.0 + (m_point * m_scalar).to_vec() + (f_point * f_scalar).to_vec(),
                            acc.1 + m_scalar + f_scalar,
                        )
                    });

            // Equation 16 in \[Sederberg et al. 1998\], with help from equation 19 from the same.
            vertex.borrow_mut().point = if factional_components.1.so_small() {
                p_naught
            } else {
                let c = (valence - 3.0) / valence;
                p_naught * c
                    + ((factional_components.0 * 3.0) / (valence * factional_components.1)).to_vec()
            };
        }

        // Calculate the new know spacings (Section 4.2.1 in \[Sederberg et al. 1998\]) and create the new
        // edges and faces which complete the subdivision.
        // let original_vertex_count = self.control_points.len();
        for (face_i, f_p) in face_points.into_iter().enumerate() {
            // Recall that for each face, a face point was constructed and stored in the
            // vector such that a given index maps the face to and from the face point.
            let face = Rc::clone(&self.faces[face_i]);
            // perim will only contain the edges which were originally part of the perimiter for the face
            let perim = TnurccFace::get_border_edges(Rc::clone(&face))
                .into_iter()
                .filter(|e| split_edge.get(e.borrow().index).is_some())
                .collect::<Vec<_>>();

            // New control point for the face
            let f_cp = Rc::new(RefCell::new(TnurccControlPoint::new(
                self.control_points.len(),
                f_p,
            )));
            f_cp.borrow_mut().valence = perim.len();

            // In essance, a new face and edge is created for every original edge on the perimiter.
            // Allocate and create them here, then, when splitting and connecting the edges, assign
            // edges and so forth. For every new face, the 0th corner is the new face point. Note that
            // the assignment of corners to the new face is not as trivial as it may initially seem,
            // since the edge splitting process is not orientation agnostic. Furthermore, when iterating
            // on the perimiter, we are able to access every point which will be asssigned as a corner to
            // one of the new faces, but we will not not have (easy) access to all corners for a single
            // face at once. Thus, the corner assignment algorithm is a little unexpected and should not
            // be attempted without a diagram (One may be provided in the comments if I am feeling
            // diligent). As a guiding principle, remember that as the index for the perimeter edge
            // increases, we traverse the perimeter in an anti-clockwise fashion.
            let mut new_faces = Vec::with_capacity(perim.len());
            let mut radial_edges = Vec::with_capacity(perim.len()); // Indexes with perim_i
            let mut edge_conjugates = Vec::with_capacity(perim.len());

            let perim_knots = perim
                .iter()
                .map(|e| e.borrow().knot_interval)
                .collect::<Vec<_>>();
            self.control_points.push(Rc::clone(&f_cp));

            (0..perim.len()).for_each(|i| {
                new_faces.push(Rc::new(RefCell::new(TnurccFace::<P> {
                    index: self.faces.len() + i,
                    edge: None,
                    corners: [Some(Rc::clone(&f_cp)), None, None, None],
                })));

                radial_edges.push(Rc::new(RefCell::new(TnurccEdge::<P> {
                    index: 0,
                    connections: [None, None, None, None],
                    face_left: None,
                    face_right: None,
                    origin: Rc::clone(&f_cp),
                    dest: Rc::clone(&dummy_point),
                    knot_interval: 0.0,
                })));
            });

            // In order to guarantee that auto-connecting the faces works as expected, we need to iterate through the
            // perimeter twice. Once to split all edges which aren't already split, collecting split conjugates as we
            // go, and another to assign faces and connect edges. Doing this all at once is difficult, as having too much
            // of the mesh up in the air at once makes knowing exactly what is where almost impossible.
            for (perim_i, edge) in perim.iter().enumerate() {
                // Some helper variables to make life a little nicer
                let edge_index = edge.borrow().index;

                // Only split edge if it shas not been split before.
                if *split_edge
                    .get(edge_index)
                    .expect("All out of bounds edges should have been filtered out on construction of perim") 
                {
                    // If the edge is already split, then the edge which was generated by the split is connected to the 
                    // current edge, since none of the radial edges have been connected yet. The match is nesessary
                    // because the conjugate may be located in different positioins depending on which face we are
                    // currently iterating.
                    edge_conjugates.push(
                        match edge
                            .borrow()
                            .get_face_side(Rc::clone(&face))
                            .expect("Edge on face perimiter should be connected to face")
                        {
                            TnurccFaceSide::Left => edge.borrow().get_connection(LeftAcw),
                            TnurccFaceSide::Right => edge.borrow().get_connection(RightCw),
                        },
                    );

                    // If the edge has been split, that means that the edge's destination is the center of the split (by convention)
                    // Guaranteed to be the case because new edges created by this algorithm were filtered out. Set the corresponding radial edge's destination to the 
                    radial_edges[perim_i].borrow_mut().dest = Rc::clone(&edge.borrow().dest);
                } else {
                    // If it is not split, split it
                    split_edge[edge_index] = true;
                    // No need to check which side is which for knot intervals because the interval is symetrical
                    let edge_control_point = TnurccEdge::split_edge(
                        Rc::clone(&edge),
                        self.edges.len(),
                        edge_points[edge_index].clone(),
                        self.control_points.len(),
                        0.5,
                    )
                    .expect("Subdivide should always be able to split an edge");
                    // The edge that results from the split
                    let pair = edge.borrow().get_connection(LeftAcw);

                    // Push split edge and new control point
                    self.edges.push(Rc::clone(&pair));
                    self.control_points.push(Rc::clone(&edge_control_point));

                    edge_conjugates.push(pair);
                    radial_edges[perim_i].borrow_mut().dest = edge_control_point;
                };
            }

            for (perim_i, edge) in perim.iter().enumerate() {
                // Some helper variables to make life a little nicer
                let next_perim_index = (perim_i + 1) % perim.len();
                let prev_perim_index = (perim_i + perim.len() - 1) % perim.len();
                let edge_face_side = edge
                    .borrow()
                    .get_face_side(Rc::clone(&self.faces[face_i]))
                    .expect("Edge on face perimiter should be connected to face");

                // Depending on the orientation of the current edge, different points must be assigned to be the corners of the face.
                // Recall that corners[0] was set in the constructor. Also note that corners are assigned in an anti-clockwise fashion,
                // which is not strictly nescessary, but makes keeping track of what is where simpler. Notice that the same corner
                // indicies for the sme new face indicies are modified every iteration regardless of orientation.
                // This is also the time to assign the correct faces to the edges, including the face comming out of the new face point.
                match edge_face_side {
                    TnurccFaceSide::Left => {
                        // Assign corners
                        new_faces[perim_i].borrow_mut().corners[2] =
                            Some(Rc::clone(&edge.borrow().origin));
                        new_faces[perim_i].borrow_mut().corners[3] =
                            Some(Rc::clone(&edge.borrow().dest));

                        new_faces[next_perim_index].borrow_mut().corners[1] =
                            Some(Rc::clone(&edge.borrow().dest));

                        // Update incoming edge on face
                        new_faces[perim_i].borrow_mut().edge = Some(Rc::clone(&edge));

                        // Assign faces
                        edge.borrow_mut().face_left = Some(Rc::clone(&new_faces[perim_i]));
                        edge_conjugates[perim_i].borrow_mut().face_left =
                            Some(Rc::clone(&new_faces[next_perim_index]));
                    }
                    TnurccFaceSide::Right => {
                        // Assign corners
                        new_faces[perim_i].borrow_mut().corners[2] =
                            Some(Rc::clone(&edge_conjugates[perim_i].borrow().dest));
                        new_faces[perim_i].borrow_mut().corners[3] =
                            Some(Rc::clone(&edge_conjugates[perim_i].borrow().origin));

                        new_faces[next_perim_index].borrow_mut().corners[1] =
                            Some(Rc::clone(&edge_conjugates[perim_i].borrow().origin));

                        // Update incoming edge on face
                        new_faces[perim_i].borrow_mut().edge =
                            Some(Rc::clone(&edge_conjugates[perim_i]));

                        // Assign faces
                        edge.borrow_mut().face_right =
                            Some(Rc::clone(&new_faces[next_perim_index]));
                        edge_conjugates[perim_i].borrow_mut().face_right =
                            Some(Rc::clone(&new_faces[perim_i]));
                    }
                };

                // Knot interval of face connecting edge point to face point.
                // Figure 10 in \[Sederberg et al. 1998\]
                let knot_interval = {
                    // We unfourtunatly require the knot interval of the original (unsplit) previous and next edge.
                    // However, since the knot interval is evenly split, if we know an edge is split, we can just
                    // multiply the knot interval by two. Edge is split if it is out of bounds for split_edge or
                    // split_edge is true.
                    let mut multiplier = 0.25;
                    if split_edge
                        .get(perim[next_perim_index].borrow().index)
                        .map_or(true, |&b| b)
                    {
                        multiplier *= 2.0;
                    }

                    if split_edge
                        .get(perim[prev_perim_index].borrow().index)
                        .map_or(true, |&b| b)
                    {
                        multiplier *= 2.0;
                    }

                    multiplier * (perim_knots[next_perim_index] + perim_knots[prev_perim_index])
                };

                // Mutate the face point to split midpoint edge so that it is ready for connection
                {
                    let mut borrow = radial_edges[perim_i].borrow_mut();
                    borrow.index = self.edges.len() + perim_i;
                    borrow.connections.fill_with(|| Some(Rc::clone(&edge)));
                    borrow.face_left = Some(Rc::clone(&new_faces[next_perim_index]));
                    borrow.face_right = Some(Rc::clone(&new_faces[perim_i]));
                    // borrow.origin (already correctly assigned in constructor)
                    // borrow.dest (assigned on edge splitting)
                    borrow.knot_interval = knot_interval;
                }
            }

            for (perim_i, edge) in perim.iter().enumerate() {
                // Some helper variables to make life a little nicer
                let next_perim_index = (perim_i + 1) % perim.len();

                // Connect radial to the perimiter
                TnurccEdge::connect(Rc::clone(&edge), Rc::clone(&radial_edges[perim_i]))
                    .expect("Edges around the perimeter should always succesfully connect to the radial edge");
                TnurccEdge::connect(Rc::clone(&edge_conjugates[perim_i]), Rc::clone(&radial_edges[perim_i]))
                    .expect("Edges around the perimeter should always succesfully connect to the radial edge");

                // Connect the radials between each other
                TnurccEdge::connect(
                    Rc::clone(&radial_edges[next_perim_index]),
                    Rc::clone(&radial_edges[perim_i]),
                )
                .expect("Radial edges should always succesfully connect between each other");

                // This will be overidden several times, not sure exactly how to deal with it without crying...
                f_cp.borrow_mut()
                    .incoming_edge
                    .replace(Rc::clone(&radial_edges[perim_i]));
                self.edges.push(Rc::clone(&radial_edges[perim_i]));
            }

            // Adding the faces into the self array is a little tricky. The first face in the new_faces arrays
            //substitutes the old face, and the rest are tacked onto the end of the faces array.
            new_faces[0].borrow_mut().index = face_i;
            self.faces[face_i] = Rc::clone(&new_faces[0]);
            new_faces.into_iter().skip(1).for_each(|f| {
                f.borrow_mut().index = self.faces.len();
                self.faces.push(f);
            });

            f_cp.borrow_mut().valence = perim.len();
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Creates a T-NURCC cube with sides of lenth `1`, lower front left point at `(0, 0, 0)`,
    /// and all verticies in the first octant.
    fn make_cube() -> Result<Tnurcc<Point3>> {
        use crate::prelude::Point3;
        let points = vec![
            Point3::from((0.0, 0.0, 0.0)), // 0
            Point3::from((0.0, 0.0, 1.0)), // 1
            Point3::from((0.0, 1.0, 1.0)), // 2
            Point3::from((0.0, 1.0, 0.0)), // 3
            Point3::from((1.0, 0.0, 0.0)), // 4
            Point3::from((1.0, 0.0, 1.0)), // 5
            Point3::from((1.0, 1.0, 1.0)), // 6
            Point3::from((1.0, 1.0, 0.0)), // 7
        ];

        let faces = vec![
            [
                // Left
                (0, vec![(1, 1.0)]),
                (1, vec![(2, 1.0)]),
                (2, vec![(3, 1.0)]),
                (3, vec![(0, 1.0)]),
            ],
            [
                // Front
                (0, vec![(4, 1.0)]),
                (4, vec![(5, 1.0)]),
                (5, vec![(1, 1.0)]),
                (1, vec![(0, 1.0)]),
            ],
            [
                // Bottom
                (0, vec![(3, 1.0)]),
                (3, vec![(7, 1.0)]),
                (7, vec![(4, 1.0)]),
                (4, vec![(0, 1.0)]),
            ],
            [
                // Right
                (4, vec![(7, 1.0)]),
                (7, vec![(6, 1.0)]),
                (6, vec![(5, 1.0)]),
                (5, vec![(4, 1.0)]),
            ],
            [
                // Back
                (3, vec![(2, 1.0)]),
                (2, vec![(6, 1.0)]),
                (6, vec![(7, 1.0)]),
                (7, vec![(3, 1.0)]),
            ],
            [
                // Top
                (1, vec![(2, 1.0)]),
                (2, vec![(6, 1.0)]),
                (6, vec![(5, 1.0)]),
                (5, vec![(1, 1.0)]),
            ],
        ];

        Tnurcc::try_new(points, faces)
    }

    #[test]
    fn t_nurcc_test_make_cube_faces() {
        let surface = make_cube();
        assert!(
            surface.is_ok(),
            "Surface was unsuccesfully created with error: {}.",
            surface.err().unwrap()
        );
        let surface = make_cube().unwrap();

        assert_eq!(surface.faces.len(), 6, "Cube does not contain 6 faces.");
        assert_eq!(
            surface.control_points.len(),
            8,
            "Cube does not contain 8 verticies."
        );
        assert_eq!(surface.edges.len(), 12, "Cube does not contain 12 edges.");
    }

    #[test]
    fn t_nurcc_test_cube_control_point_properties() {
        let surface = make_cube().unwrap();

        for p in surface.control_points.iter() {
            // Check valence
            assert_eq!(
                p.borrow().valence,
                3,
                "Point {} does not have a valence of 3.",
                p.borrow().index
            );

            // Incomin edge of the point
            let point_edge = Rc::clone(
                p.borrow()
                    .incoming_edge
                    .as_ref()
                    .expect("All points should have an incoming edge"),
            );

            // Point-based iter will rotate around the current control point
            let mut iter = TnurccAcwPointIter::from_edge(
                Rc::clone(&point_edge),
                point_edge
                    .borrow()
                    .get_point_end(Rc::clone(&p))
                    .expect("Point should be a side of its incoming edge"),
            );
            let mut next = None;

            // Point is valence 3, so there will be three points
            for _ in 0..3 {
                next = iter.next();
            }

            // Assert there are no more than 3 edges to rotate around
            let next = next.expect("Valence 3 point iters should have 3 incoming edges");
            assert!(
                iter.next().is_none(),
                "Point {} is part of an edge loop which does not close correctly. Reached {}",
                p.borrow().index,
                next.borrow().index
            );

            // Assert the next acw edge (from the last one returned by the iter)
            // is the same edge as the one it started at
            let next_point_end = next
                .borrow()
                .get_point_end(Rc::clone(&p))
                .expect("Edges reached through a point iter should be connected to that point");
            let final_edge = next.borrow().acw_edge_from_end(next_point_end);
            assert!(
                std::ptr::eq(final_edge.as_ref(), point_edge.as_ref()),
                "Iter does not rotate around point correctly. Reached {}, expected {}",
                final_edge.borrow().index,
                point_edge.borrow().index,
            );
        }
    }

    #[test]
    fn t_nurcc_test_cube_face_properties() {
        let surface = make_cube().unwrap();

        for face in surface.faces.iter() {
            let face_edge = Rc::clone(
                face.borrow()
                    .edge
                    .as_ref()
                    .expect("All faces should have a reference edge in T-NURCC"),
            );

            let mut iter = TnurccAcwFaceIter::try_from_edge(
                Rc::clone(&face_edge),
                face_edge.borrow().get_face_side(Rc::clone(face)).unwrap(),
            )
            .expect("face_edge should have Some(face) because it was cloned from face");
            let mut next = None;

            for _ in 0..4 {
                next = iter.next();
            }

            // Assert that each face has four edges
            let next = next.expect("Rectangular faces should have 4 faces to rotate around.");
            assert!(
                iter.next().is_none(),
                "Edge {} is part of a non-square face. Reached {}.",
                face_edge.borrow().index,
                next.borrow().index
            );

            // Assert the next acw edge (from the last one returned by the iter)
            // is the same edge as the one it started at
            let next_face_side = next
                .borrow()
                .get_face_side(Rc::clone(&face))
                .expect("Edges reached through a face iter should be connected to that face");
            let final_edge = next.borrow().acw_edge_from_side(next_face_side);
            assert!(
                std::ptr::eq(final_edge.as_ref(), face_edge.as_ref()),
                "Iter does not rotate around face correctly. Reached {}, expected {}",
                final_edge.borrow().index,
                face_edge.borrow().index,
            );
        }
    }

    #[test]
    fn t_nurcc_test_subdivide() {
        let mut surface = make_cube().unwrap();
        let res = surface.global_subdivide();

        assert!(!res.is_err(), "Subivide should complete succesfully");

        // Check basic geometric properties
        assert_eq!(
            surface.faces.len(),
            6 * 4,
            "Number of faces after subdivide should be 4 times the original quantity"
        );
        assert_eq!(
            surface.control_points.len(),
            (8 + 12 + 6),
            "Number of points after subdivide should be the sum of points, edges, and faces prior to subdividing");
        assert_eq!(
            surface.edges.len(),
            (12 * 2 + 4 * 6),
            "Number of edges after subdivide should be the sum of twice the count of edges prior subdividing and the sum of the number of edges on each face for each face");

        // Check indicies
        assert!(
            surface
                .faces
                .iter()
                .all(|f| std::ptr::eq(f.as_ref(), surface.faces[f.borrow().index].as_ref())),
            "Indicies for each face should match their assigned index"
        );
        assert!(
            surface.control_points.iter().all(|c| std::ptr::eq(
                c.as_ref(),
                surface.control_points[c.borrow().index].as_ref()
            )),
            "Indicies for each control point should match their assigned index"
        );
        assert!(
            surface
                .edges
                .iter()
                .all(|e| std::ptr::eq(e.as_ref(), surface.edges[e.borrow().index].as_ref())),
            "Indicies for each edge should match their assigned index"
        );

        // Make sure that edge assignments for points and faces are correct
        let poorly_referenced_surfaces = surface
            .faces
            .iter()
            .filter(|f| {
                !(f.borrow()
                    .edge
                    .as_ref()
                    .is_some_and(|e| e.borrow().get_face_side(Rc::clone(&f)).is_some()))
            })
            .map(|f| Rc::clone(&f))
            .collect::<Vec<_>>();
        assert!(poorly_referenced_surfaces.len() == 0, "All faces should have been assigned an edge on its perimeter. {} faces do not follow this", poorly_referenced_surfaces.len());

        let poorly_referenced_points = surface
            .control_points
            .iter()
            .filter(|c| {
                !(c.borrow()
                    .incoming_edge
                    .as_ref()
                    .is_some_and(|e| e.borrow().get_point_end(Rc::clone(&c)).is_some()))
            })
            .map(|c| Rc::clone(&c))
            .collect::<Vec<_>>();
        assert!(poorly_referenced_points.len() == 0, "All control points should have been assigned an incoming edge. {} points do not follow this", poorly_referenced_points.len());

        // Make sure the faces are well formed
        surface.faces.iter().for_each(|f| {
            let start_edge = Rc::clone(
                f.borrow()
                    .edge
                    .as_ref()
                    .expect("All faces should have an edge"),
            );

            // Anticlockwise traversal
            let mut acw_traverse_edge = Rc::clone(&start_edge);
            // Each face is 4 sided
            for i in 0..4 {
                acw_traverse_edge = {
                    let side = acw_traverse_edge
                        .borrow()
                        .get_face_side(Rc::clone(f))
                        .expect(format!("Face should be connected to reference edge, error on ACW traversal {} face {}", i, f.borrow().index).as_str());
                    match side {
                        TnurccFaceSide::Left => acw_traverse_edge
                            .borrow()
                            .get_connection(TnurccConnection::LeftAcw),
                        TnurccFaceSide::Right => acw_traverse_edge
                            .borrow()
                            .get_connection(TnurccConnection::RightAcw),
                    }
                };
            }

            // Clockwise traversal
            let mut cw_traverse_edge = Rc::clone(&start_edge);
            // Each face is 4 sided
            for i in 0..4 {
                cw_traverse_edge = {
                    let side = cw_traverse_edge
                        .borrow()
                        .get_face_side(Rc::clone(f))
                        .expect(format!("Face should be connected to reference edge, error on CW traversal {} face {}", i, f.borrow().index).as_str());
                    match side {
                        TnurccFaceSide::Left => cw_traverse_edge
                            .borrow()
                            .get_connection(TnurccConnection::LeftCw),
                        TnurccFaceSide::Right => cw_traverse_edge
                            .borrow()
                            .get_connection(TnurccConnection::RightCw),
                    }
                };
            }

            assert!(
                std::ptr::eq(start_edge.as_ref(), acw_traverse_edge.as_ref()),
                "Anticlockwise traversal around face index {} did not return to the start edge.",
                f.borrow().index
            );

            assert!(
                std::ptr::eq(start_edge.as_ref(), cw_traverse_edge.as_ref()),
                "Clockwise traversal around face index {} did not return to the start edge.",
                f.borrow().index
            );
        });
    }
}

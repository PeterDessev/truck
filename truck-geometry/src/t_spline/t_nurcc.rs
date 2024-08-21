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
    /// - `TnurccMalformedFace` if the corners across edges do not match.
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
    fn t_nurcc_test_make_cube_fves() {
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
                    .get_point_side(Rc::clone(&p))
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
                .get_point_side(Rc::clone(&p))
                .expect("Edges reached through a point iter should be connected to that point");
            let final_edge = next.borrow().acw_edge_from_point(next_point_end);
            assert!(
                std::ptr::eq(
                    final_edge.as_ref(),
                    point_edge.as_ref()
                ),
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
            let final_edge = next.borrow().acw_edge_from_face(next_face_side);
            assert!(
                std::ptr::eq(
                    final_edge.as_ref(),
                    face_edge.as_ref()
                ),
                "Iter does not rotate around face correctly. Reached {}, expected {}",
                final_edge.borrow().index,
                face_edge.borrow().index,
            );
        }
    }
}

//! # T-Splines
//! T-Splines are a superset of NURBS, Catmull and Clark surfaces, and B-Splines.
//! T-meshes and T-NURCCs are surfaces. It does not makes sense to have a T-mesh
//! curve or T-NURCC curve, so the semantic distinction is omitted
//!
//! # Bibliography:
//! - Sederberg, Thomas & Zheng, Jianmin & Sewell, David & Sabin, Malcolm. (1999).
//!     *Non-Uniform Recursive Subdivision Surfaces*. Proceedings of the 25th Annual
//!     Conference on Computer Graphics and Interactive Techniques, SIGGRAPH 1998.
//!     10.1145/280814.280942.
//!
//! - Sederberg, Thomas & Zheng, Jianmin & Bakenov, Almaz & Nasri, Ahmad. (2003).
//!     *T-splines and T-NURCCs*. ACM Transactions on Graphics (TOG). 22. 477-484.
//!     10.1145/882262.882295.

use crate::{prelude::*, *};
use std::cell::RefCell;
use std::rc::Rc;
use truck_base::cgmath64::control_point::ControlPoint;

pub type TmeshConnection<P> = (Option<Rc<RefCell<TmeshControlPoint<P>>>>, f64);

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TmeshConnectionType {
    Point,
    Edge,
    Tjunction,
}
/// # T-mesh control point
///
/// Described in \[Sederberg et al. 2003\].
#[derive(PartialEq, Debug)]
pub struct TmeshControlPoint<P> {
    point: P, // The control point location in Cartesian space

    // The four possible connections to other control points and thier weights.
    // They are, from index 0-3, the top, right, bottom, and left connections, respectively.
    // A connection may still have a weight even if it does not connect to another control point;
    // For details, see Figure 8 of [Sederberg et al. 2003].
    connections: [Option<TmeshConnection<P>>; 4],

    // The "absolute" knot coordinates of the control point in the context of the mesh.
    // (horizontal, virtical), RIGHT and UP are the directions in which a delta corresponds
    // to a positive increase in knot coordinates
    knot_coordinates: (f64, f64),
}

/// # T-mesh
///
/// Described in \[Sederberg et al. 2003\].
/// A T-mesh is the structure behind a T-spline. Each point may have up to four
/// possible connections with other adjacent points in the mesh. Each connection has
/// a knot interval, which may be any number greater than or equal to 0.
#[derive(PartialEq, Debug)]
pub struct Tmesh<P> {
    control_points: Vec<Rc<RefCell<TmeshControlPoint<P>>>>,

    knot_vectors: RefCell<Option<Vec<(KnotVec, KnotVec)>>>,
}

/// # TmeshDirrection
///
/// A C-style enum designed to enforce T-mesh control point directionality.
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum TmeshDirection {
    Up = 0,
    Right = 1,
    Down = 2,
    Left = 3,
}

/// # T-NURCC Control Point
///
/// Described in \[Sederberg et al. 2003\].
#[derive(Debug)]
struct TnurccControlPoint<P> {
    index: usize,
    valence: usize,
    point: P, // The control point location in Cartesian space
    incoming_edge: Option<Rc<RefCell<TnurccEdge<P>>>>,
}

struct TnurccAcwPointIter<P> {
    point: Rc<RefCell<TnurccControlPoint<P>>>,
    start: Rc<RefCell<TnurccEdge<P>>>,
    cur: Option<Rc<RefCell<TnurccEdge<P>>>>,
}

#[derive(Debug)]
struct TnurccFace<P> {
    index: usize,
    edge: Option<Rc<RefCell<TnurccEdge<P>>>>,
    corners: [Option<Rc<RefCell<TnurccControlPoint<P>>>>; 4],
}

struct TnurccAcwFaceIter<P> {
    face: Rc<RefCell<TnurccFace<P>>>,
    start: Rc<RefCell<TnurccEdge<P>>>,
    cur: Option<Rc<RefCell<TnurccEdge<P>>>>,
}

#[derive(Clone, PartialEq, Debug, Copy)]
enum TnurccConnection {
    LeftCw = 0,
    LeftAcw = 1,
    RightCw = 2,
    RightAcw = 3,
}

#[derive(Clone, PartialEq, Debug, Copy)]
enum TnurccVertexEnd {
    Origin,
    Dest,
}

#[derive(Clone, PartialEq, Debug, Copy)]
enum TnurccFaceSide {
    Left,
    Right,
}

#[derive(Debug)]
struct TnurccEdge<P> {
    index: usize,
    // Connections are always Some(con) if initialized through new
    connctions: [Option<Rc<RefCell<TnurccEdge<P>>>>; 4],

    face_left: Option<Rc<RefCell<TnurccFace<P>>>>,
    face_right: Option<Rc<RefCell<TnurccFace<P>>>>,

    origin: Rc<RefCell<TnurccControlPoint<P>>>,
    dest: Rc<RefCell<TnurccControlPoint<P>>>,

    knot_interval: f64,
}

/// # T-NURCC
///
/// Described in \[Sederberg et al. 2003\], building on material from \[Sederberg et al. 1999\].
#[derive(Debug)]
pub struct Tnurcc<P> {
    edges: Vec<Rc<RefCell<TnurccEdge<P>>>>,
    control_points: Vec<Rc<RefCell<TnurccControlPoint<P>>>>,
    extraordinary_control_points: Vec<Rc<RefCell<TnurccControlPoint<P>>>>,
    faces: Vec<Rc<RefCell<TnurccFace<P>>>>,
}

mod t_mesh;
mod t_mesh_control_point;
mod t_mesh_direction;

mod t_nurcc;
mod t_nurcc_control_point;
mod t_nurcc_edge;
mod t_nurcc_iter;
mod t_nurcc_face;
mod t_nurcc_enums;
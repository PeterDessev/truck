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

pub type TMeshConnection<P> = (Option<Rc<RefCell<TMeshControlPoint<P>>>>, f64);

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TMeshConnectionType {
    Point,
    Edge,
    Tjunction,
}
/// # T-mesh control point
///
/// Described in \[Sederberg et al. 2003\].
#[derive(PartialEq, Debug)]
pub struct TMeshControlPoint<P> {
    point: P, // The control point location in Cartesian space

    // The four possible connections to other control points and thier weights.
    // They are, from index 0-3, the top, right, bottom, and left connections, respectively.
    // A connection may still have a weight even if it does not connect to another control point;
    // For details, see Figure 8 of [Sederberg et al. 2003].
    connections: [Option<TMeshConnection<P>>; 4],

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
pub struct TMesh<P> {
    control_points: Vec<Rc<RefCell<TMeshControlPoint<P>>>>,

    knot_vectors: Option<Vec<(KnotVec, KnotVec)>>,
    bezier_domains: Option<Box<TMesh<P>>>,
}

/// # TMeshDirrection
///
/// A C-style enum designed to enforce T-mesh control point directionality.
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum TMeshDirection {
    UP = 0,
    RIGHT = 1,
    DOWN = 2,
    LEFT = 3,
}

/// # T-NURCC Control Point
///
/// Described in \[Sederberg et al. 2003\].
#[derive(Clone, PartialEq, Debug)]
pub struct TnurccControlPoint<P> {
    point: P, // The control point location in Cartesian space

    // A T-NURCC control point may have any number n connections, making it n valence.
    connections: Vec<(Option<Rc<P>>, f64)>,
}

/// # T-NURCC
///
/// Described in \[Sederberg et al. 2003\], building on material from \[Sederberg et al. 1999\].
#[derive(Clone, PartialEq, Debug)]
pub struct TNURCC<P> {
    control_points: Vec<Rc<TnurccControlPoint<P>>>,
}

mod t_mesh_direction;
mod t_mesh_control_point;
mod t_mesh;
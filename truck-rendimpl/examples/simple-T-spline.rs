//! Simple B-Spline viewer
//!
//! - Drag the mouse to rotate the model.
//! - Right-click to move the light to the camera's position.
//! - Enter "P" on the keyboard to switch between parallel projection and perspective projection of the camera.
//! - Enter "L" on the keyboard to switch the point light source/uniform light source of the light.
//! - Enter "Space" on the keyboard to switch the rendering mode for the wireframe, surface, and control polygon.
//! - Enter "Up Arrow" or "Down Arrow" to increase or decrease the number of faces used in producing the B-Spline surface.

use std::sync::Arc;
use truck_meshalgo::prelude::*;
use truck_platform::*;
use truck_rendimpl::*;
use wgpu::*;
use winit::{dpi::*, event::*, keyboard::*};
mod app;
use app::*;
use std::cell::RefCell;
use std::rc::Rc;
use truck_modeling::*;

enum RenderMode {
    Tmesh,
    ControlPolygon,
    WithControlPolygon,
}

struct MyApp {
    scene: WindowScene,
    creator: InstanceCreator,
    rotate_flag: bool,
    prev_cursor: Vector2,
    tmesh: Tmesh<Point3>,
    subdivisions: usize,
    instance: PolygonInstance,
    wireframe: WireFrameInstance,
    control_poly_instance: PolygonInstance,
    control_poly_wireframe: WireFrameInstance,
    render_mode: RenderMode,
}

impl MyApp {
    fn create_camera() -> Camera {
        let matrix = Matrix4::look_at_rh(
            Point3::new(1.0, 1.0, 1.0),
            Point3::origin(),
            Vector3::unit_y(),
        );
        Camera::perspective_camera(
            matrix.invert().unwrap(),
            Rad(std::f64::consts::PI / 4.0),
            0.1,
            40.0,
        )
    }

    fn update_render_mode(&mut self) {
        match self.render_mode {
            RenderMode::Tmesh => {
                println!("Tmesh");
                self.instance.instance_state_mut().material = Material {
                    albedo: Vector4::new(1.0, 1.0, 1.0, 1.0),
                    reflectance: 0.5,
                    roughness: 0.1,
                    ambient_ratio: 0.02,
                    background_ratio: 0.0,
                    alpha_blend: false,
                };
                self.scene.update_bind_group(&self.instance);
                self.scene.set_visibility(&self.instance, true);
                self.scene.set_visibility(&self.wireframe, true);
                self.scene
                    .set_visibility(&self.control_poly_instance, false);
                self.scene
                    .set_visibility(&self.control_poly_wireframe, false);
            }
            RenderMode::ControlPolygon => {
                println!("ControlPolygon");
                self.control_poly_instance.instance_state_mut().material = Material {
                    albedo: Vector4::new(1.0, 1.0, 1.0, 1.0),
                    reflectance: 0.5,
                    roughness: 0.1,
                    ambient_ratio: 0.02,
                    background_ratio: 0.0,
                    alpha_blend: false,
                };
                self.scene.update_bind_group(&self.instance);
                self.scene.set_visibility(&self.instance, false);
                self.scene.set_visibility(&self.wireframe, false);
                self.scene.set_visibility(&self.control_poly_instance, true);
                self.scene
                    .set_visibility(&self.control_poly_wireframe, true);
            }
            RenderMode::WithControlPolygon => {
                println!("WithControlPolygon");
                self.instance.instance_state_mut().material = Material {
                    albedo: Vector4::new(1.0, 1.0, 1.0, 1.0),
                    reflectance: 0.5,
                    roughness: 0.1,
                    ambient_ratio: 0.02,
                    background_ratio: 0.0,
                    alpha_blend: false,
                };
                self.scene.update_bind_group(&self.instance);
                self.scene.set_visibility(&self.instance, true);
                self.scene.set_visibility(&self.wireframe, false);
                self.scene
                    .set_visibility(&self.control_poly_instance, false);
                self.scene
                    .set_visibility(&self.control_poly_wireframe, true);
            }
        }
    }

    fn regenerate_surfaces(&mut self) {
        let mut polymesh = MyApp::tmesh_to_polymesh(&mut self.tmesh, false, self.subdivisions);
        let (instance, wireframe) = MyApp::load_mesh(&self.creator, &mut polymesh);

        self.scene.remove_object(&self.instance);
        self.scene.remove_object(&self.wireframe);
        self.scene.add_object(&instance);
        self.scene.add_object(&wireframe);
        self.instance = instance;
        self.wireframe = wireframe;

        self.update_render_mode();
    }

    fn tmesh_to_control_poly(input: &Tmesh<Point3>) -> truck_rendimpl::PolygonMesh {
        let points = input.control_points();
        let mut quads: Vec<Vec<usize>> = vec![];

        let upper_left_corners: Vec<(usize, &Rc<RefCell<TmeshControlPoint<Point3>>>)> = points
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.borrow().con_type(TmeshDirection::Right) == TmeshConnectionType::Point
                    && p.borrow().con_type(TmeshDirection::Down) == TmeshConnectionType::Point
            })
            .collect();

        let upper_right_corners: Vec<(usize, &Rc<RefCell<TmeshControlPoint<Point3>>>)> = points
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.borrow().con_type(TmeshDirection::Left) == TmeshConnectionType::Point
                    && p.borrow().con_type(TmeshDirection::Down) == TmeshConnectionType::Point
            })
            .collect();

        let lower_left_corners: Vec<(usize, &Rc<RefCell<TmeshControlPoint<Point3>>>)> = points
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.borrow().con_type(TmeshDirection::Right) == TmeshConnectionType::Point
                    && p.borrow().con_type(TmeshDirection::Up) == TmeshConnectionType::Point
            })
            .collect();

        let lower_right_corners: Vec<(usize, &Rc<RefCell<TmeshControlPoint<Point3>>>)> = points
            .iter()
            .enumerate()
            .filter(|(_, p)| {
                p.borrow().con_type(TmeshDirection::Left) == TmeshConnectionType::Point
                    && p.borrow().con_type(TmeshDirection::Up) == TmeshConnectionType::Point
            })
            .collect();

        for (i, ul) in upper_left_corners {
            let ur = {
                let borrow = ul
                    .borrow()
                    .navigate_until_con(TmeshDirection::Right, TmeshDirection::Down);

                let trav_res = borrow.expect("Faces must be closed");
                Rc::clone(&trav_res.0)
            };

            let ll = {
                let borrow = ul
                    .borrow()
                    .navigate_until_con(TmeshDirection::Down, TmeshDirection::Right);

                let trav_res = borrow.expect("Faces must be closed");
                Rc::clone(&trav_res.0)
            };

            let lr = {
                let borrow = ll
                    .borrow()
                    .navigate_until_con(TmeshDirection::Right, TmeshDirection::Up);

                let trav_res = borrow.expect("Faces must be closed");
                Rc::clone(&trav_res.0)
            };

            let ur_index = upper_right_corners
                .iter()
                .find(|(_, p)| std::ptr::eq(p.as_ref(), ur.as_ref()))
                .expect("Points must exist in both arrays")
                .0;

            let ll_index = lower_left_corners
                .iter()
                .find(|(_, p)| std::ptr::eq(p.as_ref(), ll.as_ref()))
                .expect("Points must exist in both arrays")
                .0;

            let lr_index = lower_right_corners
                .iter()
                .find(|(_, p)| std::ptr::eq(p.as_ref(), lr.as_ref()))
                .expect("Points must exist in both arrays")
                .0;

            quads.push([ll_index, lr_index, ur_index, i].into());
        }

        let points = input
            .control_points()
            .iter()
            .map(|p| p.borrow().point().clone())
            .collect();

        let mesh = PolygonMesh::new(
            StandardAttributes {
                positions: points,
                ..Default::default()
            },
            Faces::from_iter(quads),
        );

        mesh
    }

    fn tmesh_to_polymesh(
        input: &Tmesh<Point3>,
        closed_surface: bool,
        n: usize,
    ) -> truck_rendimpl::PolygonMesh {
        assert!(n > 1, "Number of subdivisions for converting b-splines to polygon meshes must be greater than 1");

        // Generate the point cloud associated with the B-Spline
        let mut points = Vec::new();
        for i in 0..n {
            for j in 0..n {
                let u = 1.0 / (n as f64) * (i as f64);
                let v = 1.0 / (n as f64) * (j as f64);
                points.push(input.subs(u, v).unwrap());
            }
        }

        // Create a face based on the continuity of the B-Spline:
        // A face is created by joining the points that are parametrically "adjacent"
        // to each other. Thus, in order to crate the following arrangement, assuming
        // the point (u, v) is indexed 0 in the points vector:
        //
        // (u, v') +----+  (u', v')
        //         |   /|
        //         |  / |
        //         | /  |
        // (u, v)  +----+  (u', v)
        //
        // the face vectors become: [[1, 0, 1 + N], [N, 1 + N, 0]]. In order to generalize
        // this to all points, an offset of (j + i * N) is added to each index.
        let mut faces = Vec::new();
        for i in 0..(n - 1) {
            for j in 0..(n - 1) {
                // Offset specified at the end of above.
                let offset = j + i * n;
                // Index for each point in the parallelagram in the diagram.
                // "pr" indicates prime and is equivalent to _'
                // ex: u_pr -> u'
                let u_v = offset;
                let u_v_pr = offset + 1;
                let u_pr_v = offset + n;
                let u_pr_v_pr = offset + 1 + n;

                faces.push(vec![u_v_pr, u_v, u_pr_v_pr]); // Top left face
                faces.push(vec![u_pr_v, u_pr_v_pr, u_v]); // Bottom right face
            }
        }

        // Closed surface detection (This is a very slopy way of doing this)
        // TODO: Implement better closed-surface detection
        let v_delta = (input.subs(0.0, 0.0).unwrap() - input.subs(0.0, 1.0).unwrap()).magnitude();
        let u_delta = (input.subs(0.0, 0.0).unwrap() - input.subs(1.0, 0.0).unwrap()).magnitude();

        // The function evaluates to the same value when u is equal to 0 or 1, for all v
        // That is, B(0, v) = B(1, v) for all v in [0,1]
        if closed_surface && u_delta.so_small() {
            //
            // (u, v') +----+  (u', v')
            //         |   /|
            //         |  / |
            //         | /  |
            // (u, v)  +----+  (u', v)
            //      N^2-N   0         <- points vector indicies
            // Clossing the surface on the v-axis (wrapping u over on itself)
            for j in 0..(n - 1) {
                // Offset
                let offset = j;

                // Index for each point in the parallelagram in the diagram.
                // "pr" indicates prime and is equivalent to _'
                // ex: u_pr -> u'
                let u_v = offset + n * n - n;
                let u_v_pr = offset + n * n - n + 1;
                let u_pr_v = offset;
                let u_pr_v_pr = offset + 1;

                faces.push(vec![u_v_pr, u_v, u_pr_v_pr]); // Top left face
                faces.push(vec![u_pr_v, u_pr_v_pr, u_v]); // Bottom right face
            }
        // The function evaluates to the same value for all v when u is equal to 1
        // That is, B(1, v) = P =/= B(0, v) for all v in [0,1] and P is a point in R^3
        } else if closed_surface {
            // Aquire P and push it to the points vector
            points.push(input.subs(1.0, 0.0).unwrap());
            let p = points.len() - 1;

            // Connect all open edges on the v-axis to the single point P described above
            // points indicies:
            //   N^2 - N + 1    (u, v')
            //                     |\
            //                     | \
            //                     |  \
            //                     |   * P
            //                     |  /
            //                     | /
            //                     |/
            //    N^2 - N       (u, v)
            for j in 0..(n - 1) {
                // Offset
                let offset = j;

                // Index for each point in the parallelagram in the diagram.
                // "pr" indicates prime and is equivalent to _'
                // ex: u_pr -> u'
                let u_v = offset + n * n - n;
                let u_v_pr = offset + n * n - n + 1;

                faces.push(vec![p, u_v_pr, u_v]);
            }
            // Surface is closed, so this last face is the face that wraps
            // the parameter V on itself. This arrises due to the discontinuity
            // in the statement B(1, v) = P at v = 1 and v = 0. We need a face to
            // connect the part of the surface that is at v => 1 to that is at v => 0.
            faces.push(vec![p, n * n - n, n * n - 1]);
        }

        // The function evaluates to the same value when v is equal to 0 or 1, for all u
        // That is, B(u, 0) = B(u, 1) for all u in [0,1]
        if closed_surface && v_delta.so_small() {
            // Vector indicies:
            //       0         (u, v') +----+  (u', v')
            //                         |   /|
            //                         |  / |
            //                         | /  |
            //      N-1        (u, v)  +----+  (u', v)
            //
            // Clossing the surface on the u-axis (wrapping v over on itself)
            for i in 0..(n - 1) {
                // Offset
                let offset = i * n;

                // Index for each point in the parallelagram in the diagram.
                // "pr" indicates prime and is equivalent to _'
                // ex: u_pr -> u'
                let u_v = offset + n - 1;
                let u_v_pr = offset;
                let u_pr_v = offset + n + n - 1;
                let u_pr_v_pr = offset + n;

                faces.push(vec![u_v_pr, u_v, u_pr_v_pr]); // Top left face
                faces.push(vec![u_pr_v, u_pr_v_pr, u_v]); // Bottom right face
            }
        // The function evaluates to the same value for all u when v is equal to 1
        // That is, B(u, 1) = P =/= B(u, 0) for all u in [0,1] and P is a point in R^3
        } else if closed_surface {
            // Aquire P and push it to the points vector
            points.push(input.subs(0.0, 1.0).unwrap());
            let p = points.len() - 1;

            // Connect all open edges on the u-axis to the single point P described above
            //             P
            //            /\
            //           /  \
            //          /    \
            //         /______\
            //     (u, v)   (u', v)
            //    N - 1     2*N -1    <- points vector indicies
            for i in 0..(n - 1) {
                // Offset
                let offset = i * n;

                // Index for each point in the parallelagram in the diagram.
                // "pr" indicates prime and is equivalent to _'
                // ex: u_pr -> u'
                let u_v = offset + n - 1;
                let u_v_pr = offset + 2 * n - 1;

                faces.push(vec![p, u_v, u_v_pr]);
            }
            // Surface is closed, so this last face is the face that wraps
            // the parameter V on itself. This arrises due to the discontinuity
            // in the statement B(u, 1) = P at u = 1 and u = 0. We need a face to
            // connect the part of the surface that is at u => 1 to that is at u => 0.
            faces.push(vec![p, n * n - 1, n - 1]);
        }

        let mesh = PolygonMesh::new(
            StandardAttributes {
                positions: points,
                ..Default::default()
            },
            Faces::from_iter(faces),
        );

        mesh
    }

    fn load_mesh(
        creator: &InstanceCreator,
        mesh: &mut PolygonMesh,
    ) -> (PolygonInstance, WireFrameInstance) {
        mesh.put_together_same_attrs(TOLERANCE * 2.0)
            .add_smooth_normals(0.5, false);
        mesh.remove_unused_attrs();

        let bdd_box = mesh.bounding_box();
        let (size, center) = (bdd_box.size(), bdd_box.center());
        let mat = Matrix4::from_translation(center.to_vec()) * Matrix4::from_scale(size);
        let polygon_state = PolygonState {
            matrix: mat.invert().unwrap(),
            ..Default::default()
        };
        let wire_state = WireFrameState {
            matrix: mat.invert().unwrap(),
            ..Default::default()
        };
        (
            creator.create_instance(mesh, &polygon_state),
            creator.create_instance(mesh, &wire_state),
        )
    }
}

#[async_trait(?Send)]
impl App for MyApp {
    async fn init(window: Arc<winit::window::Window>) -> MyApp {
        let points = [
            Point3::from((0.0, 0.0, 0.0)),
            Point3::from((1.0, 0.0, 1.0)),
            Point3::from((1.0, 1.0, 0.0)),
            Point3::from((0.0, 1.0, 1.0)),
        ];

        let mut tmesh = Tmesh::new(points, 1.0);

        fn average_points(a: Point3, b: Point3) -> Point3 {
            0.5 * (a + b.to_vec())
        }

        let _ = tmesh.subdivide(average_points);
        let _ = tmesh.subdivide(average_points);

        // Modify mesh so that the form is highly dependant on all elements of a point. Nescessary because if the control points
        // are on a (flat) plane, then the elements which change due to LKI (x and y) can be almost anything and the limit surface
        // will be the same. If the points are more scattered, then deviation in elements which get canceled out by the "averging"
        // nature of the LKI algorithm will become more evident in the elements which are not "averaged out".
        tmesh
            .map_point(
                Point3::from((0.25, 0.25, 0.375)),
                Point3::from((0.10, 0.25, 0.375)),
            )
            .expect("Control point is in mesh");
        tmesh
            .map_point(
                Point3::from((0.25, 0.50, 0.500)),
                Point3::from((0.30, 0.50, 0.300)),
            )
            .expect("Control point is in mesh");
        tmesh
            .map_point(
                Point3::from((0.25, 0.75, 0.625)),
                Point3::from((0.15, 0.75, 0.625)),
            )
            .expect("Control point is in mesh");
        tmesh
            .map_point(
                Point3::from((0.25, 1.00, 0.750)),
                Point3::from((0.25, 1.00, 0.200)),
            )
            .expect("Control point is in mesh");

        // Insert virtical aspect of the plus
        tmesh
            .try_absolute_local_knot_insertion((0.27, 0.25))
            .expect("Legal point insertion");
        tmesh
            .try_absolute_local_knot_insertion((0.27, 0.50))
            .expect("Legal point insertion");
        tmesh
            .try_absolute_local_knot_insertion((0.27, 0.75))
            .expect("Legal point insertion");
        tmesh
            .try_absolute_local_knot_insertion((0.27, 1.00))
            .expect("Legal point insertion");

        // Insert horrizontal aspect of the plus
        tmesh
            .try_absolute_local_knot_insertion((0.25, 0.52))
            .expect("Legal point insertion");
        tmesh
            .try_absolute_local_knot_insertion((0.50, 0.52))
            .expect("Legal point insertion");

        tmesh
            .try_absolute_local_knot_insertion((0.27, 0.52))
            .expect("Legal point insertion");

        let sample_count = 4;
        let scene_desc = WindowSceneDescriptor {
            studio: StudioConfig {
                background: Color::BLACK,
                camera: MyApp::create_camera(),
                lights: vec![Light {
                    position: Point3::new(1.0, 1.0, 1.0),
                    color: Vector3::new(1.0, 1.0, 1.0),
                    light_type: LightType::Point,
                }],
            },
            backend_buffer: BackendBufferConfig {
                sample_count,
                ..Default::default()
            },
        };
        let mut scene = WindowScene::from_window(window, &scene_desc).await;
        let creator = scene.instance_creator();

        let mut polymesh = MyApp::tmesh_to_polymesh(&tmesh, false, 20);
        let (instance, wireframe) = MyApp::load_mesh(&creator, &mut polymesh);
        scene.add_object(&instance);
        scene.add_object(&wireframe);

        let mut control_polymesh = MyApp::tmesh_to_control_poly(&tmesh);
        let (control_poly_instance, control_poly_wireframe) =
            MyApp::load_mesh(&creator, &mut control_polymesh);
        scene.add_object(&control_poly_instance);
        scene.add_object(&control_poly_wireframe);

        let mut app = MyApp {
            scene,
            creator,
            rotate_flag: false,
            prev_cursor: Vector2::zero(),
            tmesh,
            subdivisions: 20,
            instance,
            wireframe,
            control_poly_instance,
            control_poly_wireframe,
            render_mode: RenderMode::Tmesh,
        };
        app.update_render_mode();
        app
    }

    fn app_title<'a>() -> Option<&'a str> {
        Some("Simple B-Spline Viewer")
    }

    fn mouse_input(&mut self, state: ElementState, button: MouseButton) -> ControlFlow {
        match button {
            MouseButton::Left => {
                self.rotate_flag = state == ElementState::Pressed;
            }
            MouseButton::Right => {
                let (light, camera) = {
                    let desc = self.scene.studio_config_mut();
                    (&mut desc.lights[0], &desc.camera)
                };
                match light.light_type {
                    LightType::Point => {
                        light.position = camera.position();
                    }
                    LightType::Uniform => {
                        light.position = camera.position();
                        let strength = light.position.to_vec().magnitude();
                        light.position /= strength;
                    }
                }
            }
            _ => {}
        }
        Self::default_control_flow()
    }
    fn mouse_wheel(&mut self, delta: MouseScrollDelta, _: TouchPhase) -> ControlFlow {
        match delta {
            MouseScrollDelta::LineDelta(_, y) => {
                let camera = &mut self.scene.studio_config_mut().camera;
                let trans_vec = camera.eye_direction() * 0.2 * y as f64;
                camera.matrix = Matrix4::from_translation(trans_vec) * camera.matrix;
            }
            MouseScrollDelta::PixelDelta(_) => {}
        };
        Self::default_control_flow()
    }

    fn cursor_moved(&mut self, position: PhysicalPosition<f64>) -> ControlFlow {
        let position = Vector2::new(position.x, position.y);
        if self.rotate_flag {
            let matrix = &mut self.scene.studio_config_mut().camera.matrix;
            let position = Vector2::new(position.x, position.y);
            let dir2d = position - self.prev_cursor;
            if dir2d.so_small() {
                return Self::default_control_flow();
            }
            let mut axis = dir2d[1] * matrix[0].truncate();
            axis += dir2d[0] * matrix[1].truncate();
            axis /= axis.magnitude();
            let angle = dir2d.magnitude() * 0.01;
            let mat = Matrix4::from_axis_angle(axis, Rad(angle));
            *matrix = mat.invert().unwrap() * *matrix;
        }
        self.prev_cursor = position;
        Self::default_control_flow()
    }

    fn keyboard_input(&mut self, input: KeyEvent, _: bool) -> ControlFlow {
        if input.state == ElementState::Released {
            return Self::default_control_flow();
        }
        let keycode = match input.physical_key {
            PhysicalKey::Code(keycode) => keycode,
            _ => return Self::default_control_flow(),
        };
        match keycode {
            KeyCode::KeyP => {
                let camera = &mut self.scene.studio_config_mut().camera;
                *camera = match camera.projection_type() {
                    ProjectionType::Parallel => Camera::perspective_camera(
                        camera.matrix,
                        Rad(std::f64::consts::PI / 4.0),
                        0.1,
                        40.0,
                    ),
                    ProjectionType::Perspective => {
                        Camera::parallel_camera(camera.matrix, 1.0, 0.1, 40.0)
                    }
                };
            }
            KeyCode::KeyL => {
                let (light, camera) = {
                    let desc = self.scene.studio_config_mut();
                    (&mut desc.lights[0], &desc.camera)
                };
                *light = match light.light_type {
                    LightType::Point => {
                        let mut vec = camera.position();
                        vec /= vec.to_vec().magnitude();
                        Light {
                            position: vec,
                            color: Vector3::new(1.0, 1.0, 1.0),
                            light_type: LightType::Uniform,
                        }
                    }
                    LightType::Uniform => {
                        let position = camera.position();
                        Light {
                            position,
                            color: Vector3::new(1.0, 1.0, 1.0),
                            light_type: LightType::Point,
                        }
                    }
                };
            }
            KeyCode::KeyI => {
                let point = self
                    .tmesh
                    .find(Point3::from((0.5, 0.3, 0.3)))
                    .expect("Point is a valid point in mesh");

                let _ = self
                    .tmesh
                    .try_local_knot_insertion(point, TmeshDirection::Right, 0.1)
                    .expect("Local knot insertion should succeed");

                self.regenerate_surfaces();
            }
            KeyCode::Space => {
                self.render_mode = match self.render_mode {
                    RenderMode::Tmesh => RenderMode::ControlPolygon,
                    RenderMode::ControlPolygon => RenderMode::WithControlPolygon,
                    RenderMode::WithControlPolygon => RenderMode::Tmesh,
                };
                self.update_render_mode();
            }
            KeyCode::ArrowUp => {
                self.subdivisions *= 2;
                self.regenerate_surfaces();
            }
            KeyCode::ArrowDown => {
                if self.subdivisions != 1 {
                    self.subdivisions /= 2;
                    self.regenerate_surfaces();
                }
            }
            _ => {}
        }
        Self::default_control_flow()
    }

    fn render(&mut self) {
        self.scene.render_frame();
    }
}

fn main() {
    MyApp::run();
    return;
}

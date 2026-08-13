/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-!
# Degree-three vertex normalization templates

Lemma 2.3 replaces the `6 × 6` square around a degree-three vertex by one
of four finite rectilinear templates.  The replacement makes the three new
edges leave the center to the west, north, and east.  A second finite
template cyclically rotates which old incidence occupies each canonical
port, allowing one chosen edge to leave to the west.

This file transcribes those templates from Figures 2 and 3 and checks their
complete finite geometry.  Coordinates use the graph-drawing convention in
which positive `y` is north.
-/

namespace LeanTrominoes

/-- The four genuine directions, without `AxisDirection.invalid`. -/
inductive VertexSide
  | east
  | north
  | west
  | south
  deriving DecidableEq, Fintype, Repr

namespace VertexSide

/-- Embed a vertex side into the directed-axis API used by grid routes. -/
def direction : VertexSide → AxisDirection
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south

@[simp]
theorem direction_isGenuine (side : VertexSide) :
    side.direction.IsGenuine := by
  cases side <;> simp [direction, AxisDirection.IsGenuine]

end VertexSide

/-- The three canonical ports of a normalized degree-three vertex. -/
inductive CanonicalVertexPort
  | west
  | north
  | east
  deriving DecidableEq, Fintype, Repr

namespace CanonicalVertexPort

/-- Direction in which a canonical port leaves the vertex center. -/
def direction : CanonicalVertexPort → AxisDirection
  | .west => .west
  | .north => .north
  | .east => .east

@[simp]
theorem direction_isGenuine (port : CanonicalVertexPort) :
    port.direction.IsGenuine := by
  cases port <;> simp [direction, AxisDirection.IsGenuine]

end CanonicalVertexPort

namespace DegreeThreeVertexNormalization

/-- Center of every `6 × 6` replacement square. -/
def center : Cell := (3, 3)

/-- Midpoint of the replacement square's boundary in one old direction. -/
def boundaryPoint : VertexSide → Cell
  | .east => (6, 3)
  | .north => (3, 6)
  | .west => (0, 3)
  | .south => (3, 0)

/-- Old boundary direction reached from one canonical port after applying
the Figure 2 template for the omitted old direction. -/
def boundarySide
    (omitted : VertexSide) : CanonicalVertexPort → VertexSide
  | .west =>
      match omitted with
      | .north | .west => .south
      | .east | .south => .west
  | .north =>
      match omitted with
      | .north => .west
      | .east | .south | .west => .north
  | .east =>
      match omitted with
      | .east => .south
      | .north | .south | .west => .east

/-- One of the four local Figure 2 routes.  All routes start at `center`,
leave through their named canonical port, and finish at the midpoint of the
appropriate old side. -/
def route (omitted : VertexSide) : CanonicalVertexPort → List Cell
  | .west =>
      match omitted with
      | .north =>
          [(3, 3), (2, 3), (2, 2), (3, 2), (3, 1), (3, 0)]
      | .east | .south =>
          [(3, 3), (2, 3), (1, 3), (0, 3)]
      | .west =>
          [(3, 3), (2, 3), (2, 2), (3, 2), (3, 1), (3, 0)]
  | .north =>
      match omitted with
      | .north =>
          [(3, 3), (3, 4), (2, 4), (1, 4), (1, 3), (0, 3)]
      | .east | .south | .west =>
          [(3, 3), (3, 4), (3, 5), (3, 6)]
  | .east =>
      match omitted with
      | .east =>
          [(3, 3), (4, 3), (4, 2), (3, 2), (3, 1), (3, 0)]
      | .north | .south | .west =>
          [(3, 3), (4, 3), (5, 3), (6, 3)]

/-- Straight canonical route used when no cyclic port rotation is needed. -/
def identityRotationRoute : CanonicalVertexPort → List Cell
  | .west => [(3, 3), (2, 3), (1, 3), (0, 3)]
  | .north => [(3, 3), (3, 4), (3, 5), (3, 6)]
  | .east => [(3, 3), (4, 3), (5, 3), (6, 3)]

/-- The clockwise cyclic port rotation from Figure 3.  Old east enters the
new west port, old west enters the new north port, and old north enters the
new east port. -/
def clockwiseRotationRoute : CanonicalVertexPort → List Cell
  | .west =>
      [(3, 3), (2, 3), (2, 2), (3, 2), (4, 2), (5, 2), (5, 3), (6, 3)]
  | .north =>
      [(3, 3), (3, 4), (2, 4), (1, 4), (1, 3), (0, 3)]
  | .east =>
      [(3, 3), (4, 3), (4, 4), (4, 5), (3, 5), (3, 6)]

/-- Boundary side reached by one application of the clockwise rotation. -/
def clockwiseBoundarySide : CanonicalVertexPort → VertexSide
  | .west => .east
  | .north => .west
  | .east => .north

/-- A route stays in the closed replacement square. -/
def RouteInSquare (points : List Cell) : Prop :=
  ∀ point ∈ points,
    0 ≤ point.1 ∧ point.1 ≤ 6 ∧ 0 ≤ point.2 ∧ point.2 ≤ 6

/-- Distinct local routes meet only at their common vertex center. -/
def RoutesMeetOnlyAtCenter
    (routes : CanonicalVertexPort → List Cell) : Prop :=
  ∀ first second, first ≠ second →
    ∀ point, point ∈ routes first → point ∈ routes second →
      point = center

instance (points : List Cell) : Decidable (RouteInSquare points) := by
  unfold RouteInSquare
  infer_instance

instance (routes : CanonicalVertexPort → List Cell) :
    Decidable (RoutesMeetOnlyAtCenter routes) := by
  unfold RoutesMeetOnlyAtCenter
  infer_instance

/-- Every Figure 2 route has the advertised center and boundary endpoints. -/
theorem route_endpoints (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    (route omitted port).head? = some center ∧
      (route omitted port).getLast? =
        some (boundaryPoint (boundarySide omitted port)) := by
  cases omitted <;> cases port <;> native_decide

/-- Each Figure 2 route takes a genuine unit axis step at every move. -/
theorem route_unitSteps (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    (route omitted port).IsChain AxisDirection.IsUnitAxisStep := by
  cases omitted <;> cases port <;> native_decide

/-- Every Figure 2 route remains inside its replacement square. -/
theorem route_inSquare (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    RouteInSquare (route omitted port) := by
  cases omitted <;> cases port <;> native_decide

/-- The three Figure 2 routes are point-disjoint away from their common
center. -/
theorem routes_meetOnlyAtCenter (omitted : VertexSide) :
    RoutesMeetOnlyAtCenter (route omitted) := by
  cases omitted <;> native_decide

/-- The four templates use each old direction except the one omitted,
exactly once. -/
theorem boundarySides_complete (omitted : VertexSide) :
    let sides :=
      [boundarySide omitted .west, boundarySide omitted .north,
        boundarySide omitted .east]
    sides.Nodup ∧ omitted ∉ sides ∧
      ∀ side, side ≠ omitted → side ∈ sides := by
  cases omitted <;> native_decide

/-- The identity rotation has the expected center and boundary endpoints. -/
theorem identityRotationRoute_endpoints (port : CanonicalVertexPort) :
    (identityRotationRoute port).head? = some center ∧
      (identityRotationRoute port).getLast? =
        some (boundaryPoint
          (match port with
          | .west => .west
          | .north => .north
          | .east => .east)) := by
  cases port <;> native_decide

/-- The identity routes are valid, bounded, and mutually disjoint away from
the center. -/
theorem identityRotationRoute_geometry :
    (∀ port, (identityRotationRoute port).IsChain
        AxisDirection.IsUnitAxisStep ∧
      RouteInSquare (identityRotationRoute port)) ∧
      RoutesMeetOnlyAtCenter identityRotationRoute := by
  native_decide

/-- The clockwise rotation has the endpoint permutation advertised in
Figure 3. -/
theorem clockwiseRotationRoute_endpoints (port : CanonicalVertexPort) :
    (clockwiseRotationRoute port).head? = some center ∧
      (clockwiseRotationRoute port).getLast? =
        some (boundaryPoint (clockwiseBoundarySide port)) := by
  cases port <;> native_decide

/-- The clockwise routes are valid, bounded, and mutually disjoint away from
the center. -/
theorem clockwiseRotationRoute_geometry :
    (∀ port, (clockwiseRotationRoute port).IsChain
        AxisDirection.IsUnitAxisStep ∧
      RouteInSquare (clockwiseRotationRoute port)) ∧
      RoutesMeetOnlyAtCenter clockwiseRotationRoute := by
  native_decide

end DegreeThreeVertexNormalization
end LeanTrominoes

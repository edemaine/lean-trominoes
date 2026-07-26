import LeanTrominoes.OrthogonalPolylineJoin
import LeanTrominoes.PeriodicGridDrawingScaling

/-!
# Local templates for thickening an orthogonal polyline

A uniform diagonal translation of an orthogonal route is not a parallel
lane: at a right-angle bend, one translated incoming segment can cross
another translated outgoing segment.  A genuine ribbon instead offsets each
segment in its normal direction and joins consecutive offsets inside a small
rectilinear corner square.

This file defines the four directed axis directions and certifies the two
local pieces used by that construction: one offset segment and one corner
connector.  The lane distance is positive, so all emitted segments remain
nondegenerate.
-/

namespace LeanTrominoes

/-- Directed axis directions, with one total fallback for malformed input. -/
inductive AxisDirection
  | east
  | north
  | west
  | south
  | invalid
  deriving DecidableEq, Fintype, Repr

namespace AxisDirection

/-- Direction of a nondegenerate axis-aligned segment. -/
def between (first second : Cell) : AxisDirection :=
  if first.2 = second.2 then
    if first.1 < second.1 then .east
    else if second.1 < first.1 then .west
    else .invalid
  else if first.1 = second.1 then
    if first.2 < second.2 then .north
    else if second.2 < first.2 then .south
    else .invalid
  else
    .invalid

/-- Reverse directed axis. -/
def opposite : AxisDirection → AxisDirection
  | .east => .west
  | .north => .south
  | .west => .east
  | .south => .north
  | .invalid => .invalid

/-- Unit lattice step in a genuine directed axis. -/
def step : AxisDirection → Cell
  | .east => (1, 0)
  | .north => (0, 1)
  | .west => (-1, 0)
  | .south => (0, -1)
  | .invalid => (0, 0)

/-- Clockwise quarter-turn relation. -/
def TurnsRight : AxisDirection → AxisDirection → Prop
  | .east, .south
  | .south, .west
  | .west, .north
  | .north, .east => True
  | _, _ => False

instance (incoming outgoing : AxisDirection) :
    Decidable (TurnsRight incoming outgoing) := by
  cases incoming <;> cases outgoing <;>
    simp [TurnsRight] <;> infer_instance

/-- A genuine direction is one of the four axes. -/
def IsGenuine (direction : AxisDirection) : Prop :=
  direction ≠ .invalid

instance (direction : AxisDirection) :
    Decidable direction.IsGenuine := by
  unfold IsGenuine
  infer_instance

/-- A positive right-normal displacement for a directed segment. -/
def rightNormal (distance : Int) : AxisDirection → Cell
  | .east => (0, -distance)
  | .north => (distance, 0)
  | .west => (0, distance)
  | .south => (-distance, 0)
  | .invalid => (0, 0)

/-- Orthogonality makes the total direction lookup genuine. -/
theorem between_isGenuine_of_axisAligned
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (between first second).IsGenuine := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  simp only [between, IsGenuine]
  split_ifs <;> simp_all <;> omega

end AxisDirection

namespace PeriodicOrthocrossing

/-- Point on one lane at a refined copy of a source point. -/
def ribbonPoint
    (factor : Nat) (distance : Int)
    (direction : AxisDirection) (point : Cell) : Cell :=
  Cell.add (Cell.scale factor point)
    (direction.rightNormal distance)

/-- The offset copy of one directed source segment. -/
def ribbonSegment
    (factor : Nat) (distance : Int)
    (first second : Cell) : List Cell :=
  let direction := AxisDirection.between first second
  [ribbonPoint factor distance direction first,
    ribbonPoint factor distance direction second]

@[simp]
theorem ribbonSegment_head?
    (factor : Nat) (distance : Int)
    (first second : Cell) :
    (ribbonSegment factor distance first second).head? =
      some (ribbonPoint factor distance
        (AxisDirection.between first second) first) := by
  simp [ribbonSegment]

@[simp]
theorem ribbonSegment_getLast?
    (factor : Nat) (distance : Int)
    (first second : Cell) :
    (ribbonSegment factor distance first second).getLast? =
      some (ribbonPoint factor distance
        (AxisDirection.between first second) second) := by
  simp [ribbonSegment]

/-- Positive refinement keeps each offset copy of an orthogonal source
segment orthogonal and nondegenerate. -/
theorem ribbonSegment_orthogonal
    {factor : Nat} (factorPositive : 0 < factor)
    (distance : Int) {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    OrthogonalPolyline
      (ribbonSegment factor distance first second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  simp only [ribbonSegment, AxisDirection.between]
  split_ifs <;>
    simp_all [OrthogonalPolyline, ribbonPoint,
      AxisDirection.rightNormal, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      Cell.add, Cell.scale] <;>
    omega

/-- Middle point of a rectilinear connector between the incoming and
outgoing normal offsets at one source bend. -/
def ribbonCornerMiddle
    (factor : Nat) (distance : Int) (point : Cell)
    (incoming outgoing : AxisDirection) : Cell :=
  Cell.add
    (Cell.add (Cell.scale factor point)
      (incoming.rightNormal distance))
    (outgoing.rightNormal distance)

/-- Connect two normal offsets at a source point.  Straight motion needs
only the common point; a reversal is one straight segment; a proper turn
uses the opposite corner of the normal-offset rectangle. -/
def ribbonCorner
    (factor : Nat) (distance : Int) (point : Cell)
    (incoming outgoing : AxisDirection) : List Cell :=
  let first := ribbonPoint factor distance incoming point
  let last := ribbonPoint factor distance outgoing point
  if incoming = outgoing then
    [first]
  else if outgoing = incoming.opposite then
    [first, last]
  else
    [first,
      ribbonCornerMiddle factor distance point incoming outgoing,
      last]

@[simp]
theorem ribbonCorner_head?
    (factor : Nat) (distance : Int) (point : Cell)
    (incoming outgoing : AxisDirection) :
    (ribbonCorner factor distance point incoming outgoing).head? =
      some (ribbonPoint factor distance incoming point) := by
  unfold ribbonCorner
  split_ifs <;> rfl

@[simp]
theorem ribbonCorner_getLast?
    (factor : Nat) (distance : Int) (point : Cell)
    (incoming outgoing : AxisDirection) :
    (ribbonCorner factor distance point incoming outgoing).getLast? =
      some (ribbonPoint factor distance outgoing point) := by
  by_cases same : incoming = outgoing
  · subst outgoing
    simp [ribbonCorner]
  · unfold ribbonCorner
    simp only [same, ↓reduceIte]
    split_ifs <;> rfl

/-- Every local connector between genuine directions is an orthogonal
polyline.  Positivity prevents the reversal and proper-turn pieces from
collapsing. -/
theorem ribbonCorner_orthogonal
    (factor : Nat) {distance : Int} (distancePositive : 0 < distance)
    (point : Cell) {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine) :
    OrthogonalPolyline
      (ribbonCorner factor distance point incoming outgoing) := by
  rcases point with ⟨pointX, pointY⟩
  cases incoming <;> cases outgoing <;>
    simp_all [AxisDirection.IsGenuine, ribbonCorner,
      AxisDirection.opposite, ribbonPoint, ribbonCornerMiddle,
      AxisDirection.rightNormal, OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical, Cell.add, Cell.scale] <;>
    omega

/-- Offset a complete source polyline, inserting one certified corner
connector between every two consecutive offset segments. -/
def ribbonPolyline
    (factor : Nat) (distance : Int) : List Cell → List Cell
  | [] => []
  | [point] => [Cell.scale factor point]
  | first :: second :: [] =>
      ribbonSegment factor distance first second
  | first :: second :: third :: rest =>
      joinAtEndpoint
        (ribbonSegment factor distance first second)
        (joinAtEndpoint
          (ribbonCorner factor distance second
            (AxisDirection.between first second)
            (AxisDirection.between second third))
          (ribbonPolyline factor distance (second :: third :: rest)))
termination_by points => points.length

/-- Total expression for the final point of a ribbon built from a source
polyline with at least two points. -/
def ribbonPolylineFinish
    (factor : Nat) (distance : Int) :
    (first second : Cell) → List Cell → Cell
  | first, second, [] =>
      ribbonPoint factor distance
        (AxisDirection.between first second) second
  | _, second, third :: rest =>
      ribbonPolylineFinish factor distance second third rest

/-- Total first endpoint of the generated ribbon. -/
def ribbonPolylineStart
    (factor : Nat) (distance : Int) : List Cell → Cell
  | [] => (0, 0)
  | [point] => Cell.scale factor point
  | first :: second :: _ =>
      ribbonPoint factor distance
        (AxisDirection.between first second) first

/-- Total final endpoint of the generated ribbon. -/
def ribbonPolylineEnd
    (factor : Nat) (distance : Int) : List Cell → Cell
  | [] => (0, 0)
  | [point] => Cell.scale factor point
  | first :: second :: rest =>
      ribbonPolylineFinish factor distance first second rest

@[simp]
theorem ribbonPolyline_cons_cons_head?
    (factor : Nat) (distance : Int)
    (first second : Cell) (rest : List Cell) :
    (ribbonPolyline factor distance
      (first :: second :: rest)).head? =
        some (ribbonPoint factor distance
          (AxisDirection.between first second) first) := by
  cases rest with
  | nil =>
      simp [ribbonPolyline]
  | cons third rest =>
      simp [ribbonPolyline, joinAtEndpoint]

@[simp]
theorem ribbonPolyline_cons_cons_getLast?
    (factor : Nat) (distance : Int)
    (first second : Cell) (rest : List Cell) :
    (ribbonPolyline factor distance
      (first :: second :: rest)).getLast? =
        some (ribbonPolylineFinish factor distance
          first second rest) := by
  induction rest generalizing first second with
  | nil =>
      simp [ribbonPolyline, ribbonPolylineFinish]
  | cons third rest induction =>
      rw [ribbonPolyline]
      apply joinAtEndpoint_getLast?
      · exact ribbonSegment_getLast? factor distance first second
      · apply joinAtEndpoint_head?
        exact ribbonCorner_head? factor distance second
          (AxisDirection.between first second)
          (AxisDirection.between second third)
      · apply joinAtEndpoint_getLast?
        · exact ribbonCorner_getLast? factor distance second
            (AxisDirection.between first second)
            (AxisDirection.between second third)
        · exact ribbonPolyline_cons_cons_head?
            factor distance second third rest
        · simpa [ribbonPolylineFinish] using
            induction (first := second) (second := third)

/-- Every nonempty source route gives the generated ribbon its advertised
total first endpoint. -/
theorem ribbonPolyline_head?_eq_some_start
    (factor : Nat) (distance : Int)
    {points : List Cell} (nonempty : points ≠ []) :
    (ribbonPolyline factor distance points).head? =
      some (ribbonPolylineStart factor distance points) := by
  cases points with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil =>
          simp [ribbonPolyline, ribbonPolylineStart]
      | cons second rest =>
          simpa [ribbonPolylineStart] using
            ribbonPolyline_cons_cons_head?
              factor distance first second rest

/-- Every nonempty source route gives the generated ribbon its advertised
total final endpoint. -/
theorem ribbonPolyline_getLast?_eq_some_end
    (factor : Nat) (distance : Int)
    {points : List Cell} (nonempty : points ≠ []) :
    (ribbonPolyline factor distance points).getLast? =
      some (ribbonPolylineEnd factor distance points) := by
  cases points with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil =>
          simp [ribbonPolyline, ribbonPolylineEnd]
      | cons second rest =>
          simpa [ribbonPolylineEnd] using
            ribbonPolyline_cons_cons_getLast?
              factor distance first second rest

/-- The complete normal-offset construction preserves orthogonality. -/
theorem ribbonPolyline_orthogonal
    {factor : Nat} (factorPositive : 0 < factor)
    {distance : Int} (distancePositive : 0 < distance)
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points) :
    OrthogonalPolyline
      (ribbonPolyline factor distance points) := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [ribbonPolyline, OrthogonalPolyline]
  | singleton point =>
      simp [ribbonPolyline, OrthogonalPolyline]
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            OrthogonalPolyline (second :: rest))
      cases rest with
      | nil =>
          simpa [ribbonPolyline] using
            ribbonSegment_orthogonal factorPositive distance
              parts.1
      | cons third rest =>
          have nextParts :=
            (List.isChain_cons_cons.mp parts.2 :
              (GridSegment.mk second third).IsAxisAligned ∧
                OrthogonalPolyline (third :: rest))
          have segmentOrthogonal :=
            ribbonSegment_orthogonal factorPositive distance
              parts.1
          have cornerOrthogonal :=
            ribbonCorner_orthogonal factor distancePositive second
              (AxisDirection.between_isGenuine_of_axisAligned
                parts.1)
              (AxisDirection.between_isGenuine_of_axisAligned
                nextParts.1)
          have tailOrthogonal :
              OrthogonalPolyline
                (ribbonPolyline factor distance
                  (second :: third :: rest)) :=
            tailInduction second parts.2
          have cornerAndTail :=
            cornerOrthogonal.joinAtEndpoint tailOrthogonal
              (ribbonCorner_getLast? factor distance second
                (AxisDirection.between first second)
                (AxisDirection.between second third))
              (ribbonPolyline_cons_cons_head?
                factor distance second third rest)
          simpa [ribbonPolyline] using
            segmentOrthogonal.joinAtEndpoint cornerAndTail
              (ribbonSegment_getLast?
                factor distance first second)
              (joinAtEndpoint_head?
                (ribbonCorner_head? factor distance second
                  (AxisDirection.between first second)
                  (AxisDirection.between second third)))

end PeriodicOrthocrossing
end LeanTrominoes

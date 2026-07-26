import LeanTrominoes.OrthogonalPolylineRibbon
import Mathlib.Data.List.Range

/-!
# Unit subdivision of orthogonal polylines

The ribbon construction works one lattice vertex at a time.  This file
refines each nondegenerate axis-aligned source segment into its ordered list
of unit lattice steps.  The subdivision includes both original endpoints,
preserves the directed axis, and remains an orthogonal polyline.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Manhattan length of a segment.  On an axis-aligned segment this is its
ordinary lattice length. -/
def segmentLength (first second : Cell) : Nat :=
  (second.1 - first.1).natAbs +
    (second.2 - first.2).natAbs

/-- The ordered unit subdivision of one directed lattice segment, including
both endpoints.  Malformed input is total but is used only under an
axis-alignment hypothesis. -/
def unitSegmentPoints (first second : Cell) : List Cell :=
  let direction := between first second
  (List.range (segmentLength first second + 1)).map fun index : Nat =>
    Cell.add first (Cell.scale (index : Int) direction.step)

@[simp]
theorem unitSegmentPoints_length
    (first second : Cell) :
    (unitSegmentPoints first second).length =
      segmentLength first second + 1 := by
  simp [unitSegmentPoints]

@[simp]
theorem unitSegmentPoints_head?
    (first second : Cell) :
    (unitSegmentPoints first second).head? = some first := by
  rw [unitSegmentPoints, List.head?_map, List.head?_range]
  simp [Cell.add, Cell.scale]

/-- Moving by the computed lattice length in the computed direction reaches
the final endpoint of an orthogonal segment. -/
theorem add_length_step_eq_second_of_axisAligned
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    Cell.add first
        (Cell.scale (segmentLength first second)
          (between first second).step) =
      second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  rcases aligned with
      ⟨horizontal, nondegenerate⟩ |
      ⟨vertical, nondegenerate⟩
  · subst secondY
    by_cases forward : firstX < secondX
    · have castLength :
          ((secondX - firstX).natAbs : Int) =
            secondX - firstX :=
        Int.natAbs_of_nonneg (by omega)
      simp [segmentLength, between, forward, step,
        Cell.add, Cell.scale, castLength]
    · have backward : secondX < firstX := by omega
      have castLength :
          ((secondX - firstX).natAbs : Int) =
            firstX - secondX := by
        rw [show secondX - firstX =
          -(firstX - secondX) by omega, Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      simp [segmentLength, between, forward, backward, step,
        Cell.add, Cell.scale, castLength]
  · subst secondX
    by_cases forward : firstY < secondY
    · have castLength :
          ((secondY - firstY).natAbs : Int) =
            secondY - firstY :=
        Int.natAbs_of_nonneg (by omega)
      simp [segmentLength, between, forward, step,
        Cell.add, Cell.scale, castLength, nondegenerate]
    · have backward : secondY < firstY := by omega
      have castLength :
          ((secondY - firstY).natAbs : Int) =
            firstY - secondY := by
        rw [show secondY - firstY =
          -(firstY - secondY) by omega, Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      simp [segmentLength, between, forward, backward, step,
        Cell.add, Cell.scale, castLength, nondegenerate]

/-- A nondegenerate axis-aligned segment has positive lattice length. -/
theorem segmentLength_positive_of_axisAligned
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    0 < segmentLength first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at aligned
  rcases aligned with
      ⟨horizontal, nondegenerate⟩ |
      ⟨vertical, nondegenerate⟩
  · unfold segmentLength
    rw [show secondY - firstY = 0 by omega]
    simp only [Int.natAbs_zero, add_zero, Int.natAbs_pos]
    omega
  · unfold segmentLength
    rw [show secondX - firstX = 0 by omega]
    simp only [Int.natAbs_zero, zero_add, Int.natAbs_pos]
    omega

@[simp]
theorem unitSegmentPoints_getLast?
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (unitSegmentPoints first second).getLast? = some second := by
  rw [unitSegmentPoints, List.getLast?_map,
    List.getLast?_range]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel]
  exact congrArg some
    (add_length_step_eq_second_of_axisAligned aligned)

/-- Consecutive points in a generated unit segment retain the original
directed axis. -/
theorem unitSegmentPoints_direction
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (unitSegmentPoints first second).IsChain fun source target =>
      between source target = between first second := by
  rw [unitSegmentPoints, List.isChain_map,
    List.isChain_range_succ]
  intro index indexLt
  have genuine :=
    between_isGenuine_of_axisAligned aligned
  cases direction : between first second <;>
    simp_all [IsGenuine, step, Cell.add, Cell.scale, between] <;>
    omega

/-- One step of a unit orthogonal polyline. -/
def IsUnitAxisStep (source target : Cell) : Prop :=
  ∃ direction : AxisDirection,
    direction.IsGenuine ∧
      target = Cell.add source direction.step

instance (source target : Cell) :
    Decidable (IsUnitAxisStep source target) := by
  unfold IsUnitAxisStep
  infer_instance

/-- Every interior vertex of a directed route is straight or a turn, never
an immediate reversal along the axis just traversed. -/
def HasNoImmediateReversal : List Cell → Prop
  | first :: center :: next :: rest =>
      between center next ≠
          (between first center).opposite ∧
        HasNoImmediateReversal (center :: next :: rest)
  | _ => True

/-- Taking one genuine cardinal step computes that same directed axis. -/
theorem between_add_step
    (source : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    between source (Cell.add source direction.step) =
      direction := by
  rcases source with ⟨sourceX, sourceY⟩
  cases direction <;>
    simp_all [IsGenuine, between, step, Cell.add]

/-- The computed direction of a unit step is genuine. -/
theorem between_isGenuine_of_unitAxisStep
    {source target : Cell}
    (unit : IsUnitAxisStep source target) :
    (between source target).IsGenuine := by
  rcases unit with ⟨direction, genuine, rfl⟩
  rw [between_add_step source genuine]
  exact genuine

/-- A unit step can be reconstructed from its computed direction. -/
theorem add_between_step_eq_of_unitAxisStep
    {source target : Cell}
    (unit : IsUnitAxisStep source target) :
    target = Cell.add source (between source target).step := by
  rcases unit with ⟨direction, genuine, rfl⟩
  rw [between_add_step source genuine]

/-- Every consecutive pair emitted for one segment is a genuine unit step. -/
theorem unitSegmentPoints_unitSteps
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (unitSegmentPoints first second).IsChain IsUnitAxisStep := by
  rw [unitSegmentPoints, List.isChain_map,
    List.isChain_range_succ]
  intro index indexLt
  let direction := between first second
  refine ⟨direction,
    between_isGenuine_of_axisAligned aligned, ?_⟩
  rcases first with ⟨firstX, firstY⟩
  cases directionEquation : direction <;>
    simp_all [direction, step, Cell.add, Cell.scale] <;>
    omega

/-- A computed genuine direction witnesses that its endpoints form a
nondegenerate axis-aligned segment. -/
theorem isAxisAligned_of_between_isGenuine
    {first second : Cell}
    (genuine : (between first second).IsGenuine) :
    (GridSegment.mk first second).IsAxisAligned := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between, IsGenuine] at genuine
  split_ifs at genuine <;>
    simp_all [GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
    omega

/-- Unit subdivision preserves orthogonality. -/
theorem unitSegmentPoints_orthogonal
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (unitSegmentPoints first second) := by
  apply (unitSegmentPoints_direction aligned).imp
  intro source target direction
  have genuine :=
    between_isGenuine_of_axisAligned aligned
  apply isAxisAligned_of_between_isGenuine
  rw [direction]
  exact genuine

/-- Ordered unit subdivision of every segment of a source polyline. -/
def unitSubdividePolyline : List Cell → List Cell
  | [] => []
  | [point] => [point]
  | first :: second :: rest =>
      joinAtEndpoint
        (unitSegmentPoints first second)
        (unitSubdividePolyline (second :: rest))
termination_by points => points.length

@[simp]
theorem unitSubdividePolyline_nil :
    unitSubdividePolyline [] = [] :=
  by simp [unitSubdividePolyline]

@[simp]
theorem unitSubdividePolyline_singleton (point : Cell) :
    unitSubdividePolyline [point] = [point] :=
  by simp [unitSubdividePolyline]

/-- Subdivision preserves the first endpoint of every nonempty route. -/
theorem unitSubdividePolyline_head?
    {points : List Cell} (nonempty : points ≠ []) :
    (unitSubdividePolyline points).head? = points.head? := by
  cases points with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil =>
          simp
      | cons second rest =>
          rw [unitSubdividePolyline]
          simpa using joinAtEndpoint_head?
            (unitSegmentPoints_head? first second)

/-- Subdivision preserves the final endpoint of every nonempty orthogonal
route. -/
theorem unitSubdividePolyline_getLast?
    {points : List Cell} (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (unitSubdividePolyline points).getLast? =
      points.getLast? := by
  induction points using List.twoStepInduction with
  | nil => exact (nonempty rfl).elim
  | singleton point =>
      simp
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      rw [unitSubdividePolyline]
      have tailHead :
          (unitSubdividePolyline
            (second :: rest)).head? = some second := by
        simpa using unitSubdividePolyline_head?
          (points := second :: rest) (by simp)
      have tailLast :=
        tailInduction second (by simp) parts.2
      rw [joinAtEndpoint_getLast?
        (unitSegmentPoints_getLast? parts.1)
        tailHead tailLast]
      exact (List.getLast?_eq_some_getLast
        (by simp : second :: rest ≠ [])).symm

/-- Subdivision preserves orthogonality. -/
theorem unitSubdividePolyline_orthogonal
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (unitSubdividePolyline points) := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [PeriodicOrthocrossing.OrthogonalPolyline]
  | singleton point =>
      simp [PeriodicOrthocrossing.OrthogonalPolyline]
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      rw [unitSubdividePolyline]
      apply
        (unitSegmentPoints_orthogonal parts.1).joinAtEndpoint
          (tailInduction second parts.2)
          (unitSegmentPoints_getLast? parts.1)
      simpa using unitSubdividePolyline_head?
        (points := second :: rest) (by simp)

/-- The whole subdivided route consists entirely of genuine unit steps. -/
theorem unitSubdividePolyline_unitSteps
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (unitSubdividePolyline points).IsChain IsUnitAxisStep := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      rw [unitSubdividePolyline]
      apply List.IsChain.joinAtEndpoint
        (unitSegmentPoints_unitSteps parts.1)
        (tailInduction second parts.2)
        (unitSegmentPoints_getLast? parts.1)
      simpa using unitSubdividePolyline_head?
        (points := second :: rest) (by simp)

/-- A route with at least one source segment still has at least two points
after unit subdivision. -/
theorem unitSubdividePolyline_length_ge_two
    {first second : Cell} {rest : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (first :: second :: rest)) :
    2 ≤
      (unitSubdividePolyline
        (first :: second :: rest)).length := by
  have aligned :=
    (List.isChain_cons_cons.mp orthogonal).1
  have positive :=
    segmentLength_positive_of_axisAligned aligned
  rw [unitSubdividePolyline]
  simp [joinAtEndpoint]
  omega

end AxisDirection
end LeanTrominoes

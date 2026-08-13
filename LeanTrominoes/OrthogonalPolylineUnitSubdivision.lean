/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- The four direction constructors are characterized by their coordinate
equalities and strict inequalities. -/
theorem between_eq_east_iff (first second : Cell) :
    between first second = .east ↔
      first.2 = second.2 ∧ first.1 < second.1 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all

theorem between_eq_north_iff (first second : Cell) :
    between first second = .north ↔
      first.1 = second.1 ∧ first.2 < second.2 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all

theorem between_eq_west_iff (first second : Cell) :
    between first second = .west ↔
      first.2 = second.2 ∧ second.1 < first.1 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all <;> omega

theorem between_eq_south_iff (first second : Cell) :
    between first second = .south ↔
      first.1 = second.1 ∧ second.2 < first.2 := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between]
  split_ifs <;> simp_all <;> omega

/-- Reversing a genuine directed segment computes the opposite cardinal
direction. -/
theorem between_reverse_eq_opposite
    {first second : Cell}
    (genuine : (between first second).IsGenuine) :
    between second first =
      (between first second).opposite := by
  cases direction : between first second with
  | invalid =>
      simp [direction, IsGenuine] at genuine
  | east =>
      have data :=
        (between_eq_east_iff first second).mp direction
      rw [(between_eq_west_iff second first).mpr
        ⟨data.1.symm, data.2⟩]
      simp [direction, opposite]
  | north =>
      have data :=
        (between_eq_north_iff first second).mp direction
      rw [(between_eq_south_iff second first).mpr
        ⟨data.1.symm, data.2⟩]
      simp [direction, opposite]
  | west =>
      have data :=
        (between_eq_west_iff first second).mp direction
      rw [(between_eq_east_iff second first).mpr
        ⟨data.1.symm, data.2⟩]
      simp [direction, opposite]
  | south =>
      have data :=
        (between_eq_south_iff first second).mp direction
      rw [(between_eq_north_iff second first).mpr
        ⟨data.1.symm, data.2⟩]
      simp [direction, opposite]

/-- Translating both endpoints preserves their computed direction. -/
@[simp]
theorem between_add_left
    (offset first second : Cell) :
    between (Cell.add offset first)
        (Cell.add offset second) =
      between first second := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [between, Cell.add]
  split_ifs <;> simp_all <;> omega

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

/-- A genuine cardinal direction is different from its opposite. -/
theorem ne_opposite_of_isGenuine
    {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    direction ≠ direction.opposite := by
  cases direction <;>
    simp_all [IsGenuine, opposite]

/-- Taking the opposite cardinal direction twice is the identity. -/
@[simp]
theorem opposite_opposite (direction : AxisDirection) :
    direction.opposite.opposite = direction := by
  cases direction <;> rfl

/-- A route whose every step has one fixed genuine direction cannot
immediately reverse. -/
theorem hasNoImmediateReversal_of_constantDirection
    {points : List Cell} {direction : AxisDirection}
    (directions :
      points.IsChain fun first second =>
        between first second = direction)
    (genuine : direction.IsGenuine) :
    HasNoImmediateReversal points := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [HasNoImmediateReversal]
  | cons_cons first second rest _ tailInduction =>
      cases rest with
      | nil =>
          simp [HasNoImmediateReversal]
      | cons third rest =>
          have firstParts :=
            List.isChain_cons_cons.mp directions
          have secondParts :=
            List.isChain_cons_cons.mp firstParts.2
          constructor
          · rw [firstParts.1, secondParts.1]
            exact ne_opposite_of_isGenuine genuine
          · exact
              tailInduction second firstParts.2

/-- The unit points generated for one segment have no immediate reversal. -/
theorem unitSegmentPoints_hasNoImmediateReversal
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    HasNoImmediateReversal
      (unitSegmentPoints first second) := by
  exact
    hasNoImmediateReversal_of_constantDirection
      (unitSegmentPoints_direction aligned)
      (between_isGenuine_of_axisAligned aligned)

/-- A list of length at least two exposes its first two entries. -/
private theorem exists_eq_cons_cons_of_length_ge_two
    {α : Type*} {items : List α}
    (length : 2 ≤ items.length) :
    ∃ first second rest,
      items = first :: second :: rest := by
  cases items with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          exact ⟨first, second, rest, rfl⟩

/-- A list of length at least two exposes its final two entries. -/
private theorem exists_eq_append_cons_cons_of_length_ge_two
    {α : Type*} {items : List α}
    (length : 2 ≤ items.length) :
    ∃ leading before last,
      items = leading ++ [before, last] := by
  induction items with
  | nil =>
      simp at length
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp at length
      | cons second rest =>
          cases rest with
          | nil =>
              exact ⟨[], first, second, rfl⟩
          | cons third rest =>
              have tailLength :
                  2 ≤ (second :: third :: rest).length := by
                simp
              rcases induction tailLength with
                ⟨leading, before, last, equation⟩
              exact
                ⟨first :: leading, before, last, by
                  simp [equation]⟩

/-- Splicing two no-reversal routes at a shared middle point preserves the
property when the one newly adjacent pair of directions is compatible. -/
theorem HasNoImmediateReversal.append_boundary
    {leading : List Cell}
    {before middle after : Cell} {rest : List Cell}
    (left :
      HasNoImmediateReversal
        (leading ++ [before, middle]))
    (right :
      HasNoImmediateReversal
        (middle :: after :: rest))
    (boundary :
      between middle after ≠
        (between before middle).opposite) :
    HasNoImmediateReversal
      (leading ++ before :: middle :: after :: rest) := by
  induction leading with
  | nil =>
      exact ⟨boundary, right⟩
  | cons first leading induction =>
      cases leading with
      | nil =>
          exact ⟨left.1, boundary, right⟩
      | cons second rest =>
          cases rest <;>
            exact
              ⟨left.1,
                induction left.2⟩

/-- Translating every point of a route preserves the absence of immediate
reversals. -/
theorem HasNoImmediateReversal.translate
    {points : List Cell}
    (noReversal : HasNoImmediateReversal points)
    (offset : Cell) :
    HasNoImmediateReversal
      (points.map (Cell.add offset)) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [HasNoImmediateReversal]
  | cons_cons first center rest _ tailInduction =>
      cases rest with
      | nil =>
          simp [HasNoImmediateReversal]
      | cons next rest =>
          constructor
          · simpa using
              noReversal.1
          · exact
              tailInduction center noReversal.2

/-- Reversing an orthogonal route preserves the absence of immediate
reversals. -/
theorem HasNoImmediateReversal.reverse
    {points : List Cell}
    (noReversal : HasNoImmediateReversal points)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    HasNoImmediateReversal points.reverse := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [HasNoImmediateReversal]
  | cons_cons first second rest _ tailInduction =>
      cases rest with
      | nil =>
          simp [HasNoImmediateReversal]
      | cons third rest =>
          have orthogonalParts :=
            (List.isChain_cons_cons.mp orthogonal :
              (GridSegment.mk first second).IsAxisAligned ∧
                PeriodicOrthocrossing.OrthogonalPolyline
                  (second :: third :: rest))
          have noReversalParts :
              between second third ≠
                  (between first second).opposite ∧
                HasNoImmediateReversal
                  (second :: third :: rest) :=
            noReversal
          have tailNoReversal :=
            tailInduction second noReversalParts.2
              orthogonalParts.2
          have tailEquation :
              (second :: third :: rest).reverse =
                rest.reverse ++ [third, second] := by
            simp
          rw [tailEquation] at tailNoReversal
          have secondAligned :=
            (List.isChain_cons_cons.mp
              orthogonalParts.2).1
          have reversedBoundary :
              between second first ≠
                (between third second).opposite := by
            rw [between_reverse_eq_opposite
                (between_isGenuine_of_axisAligned
                  orthogonalParts.1),
              between_reverse_eq_opposite
                (between_isGenuine_of_axisAligned
                  secondAligned),
              opposite_opposite]
            exact noReversalParts.1.symm
          have joined :=
            HasNoImmediateReversal.append_boundary
              tailNoReversal
              (by simp [HasNoImmediateReversal] :
                HasNoImmediateReversal [second, first])
              reversedBoundary
          simpa [List.reverse_cons,
            List.append_assoc] using joined

/-- The final unit step of a subdivided segment retains the segment's
original direction. -/
theorem unitSegmentPoints_lastDirection
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    ∃ leading before,
      unitSegmentPoints first second =
          leading ++ [before, second] ∧
        between before second = between first second := by
  have positive :=
    segmentLength_positive_of_axisAligned aligned
  have length :
      2 ≤ (unitSegmentPoints first second).length := by
    rw [unitSegmentPoints_length]
    omega
  rcases
      exists_eq_append_cons_cons_of_length_ge_two length with
    ⟨leading, before, last, equation⟩
  have lastEqual : last = second := by
    have lastEndpoint :=
      unitSegmentPoints_getLast? aligned
    rw [equation] at lastEndpoint
    simpa using lastEndpoint
  subst last
  refine ⟨leading, before, equation, ?_⟩
  have directionChain :=
    unitSegmentPoints_direction aligned
  rw [equation] at directionChain
  have suffixChain :
      [before, second].IsChain fun source target =>
        between source target = between first second :=
    (List.isChain_append.mp directionChain).2.1
  simpa using suffixChain

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

/-- The first unit step of a nondegenerate subdivided polyline retains the
direction of its first source segment. -/
theorem unitSubdividePolyline_firstDirection
    {first second : Cell} {rest : List Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    ∃ after tail,
      unitSubdividePolyline (first :: second :: rest) =
          first :: after :: tail ∧
        between first after = between first second := by
  have positive :=
    segmentLength_positive_of_axisAligned aligned
  have length :
      2 ≤ (unitSegmentPoints first second).length := by
    rw [unitSegmentPoints_length]
    omega
  rcases exists_eq_cons_cons_of_length_ge_two length with
    ⟨actualFirst, after, segmentRest, segmentEquation⟩
  have firstEqual : actualFirst = first := by
    have firstEndpoint :=
      unitSegmentPoints_head? first second
    rw [segmentEquation] at firstEndpoint
    simpa using firstEndpoint
  subst actualFirst
  have firstDirection :
      between first after = between first second := by
    have directionChain :=
      unitSegmentPoints_direction aligned
    rw [segmentEquation] at directionChain
    exact (List.isChain_cons_cons.mp directionChain).1
  refine
    ⟨after,
      segmentRest ++
        (unitSubdividePolyline (second :: rest)).tail,
      ?_, firstDirection⟩
  rw [unitSubdividePolyline, joinAtEndpoint,
    segmentEquation]
  simp

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

/-- Unit subdivision preserves the absence of immediate reversals. -/
theorem unitSubdividePolyline_hasNoImmediateReversal
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (noReversal : HasNoImmediateReversal points) :
    HasNoImmediateReversal
      (unitSubdividePolyline points) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [unitSubdividePolyline,
        HasNoImmediateReversal]
  | cons_cons first second rest _ tailInduction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      cases rest with
      | nil =>
          rw [unitSubdividePolyline]
          simpa [joinAtEndpoint] using
            unitSegmentPoints_hasNoImmediateReversal
              orthogonalParts.1
      | cons third rest =>
          have noReversalParts :
              between second third ≠
                  (between first second).opposite ∧
                HasNoImmediateReversal
                  (second :: third :: rest) :=
            noReversal
          have tailNoReversal :=
            tailInduction second orthogonalParts.2
              noReversalParts.2
          rcases
              unitSegmentPoints_lastDirection
                orthogonalParts.1 with
            ⟨leading, before, segmentEquation,
              incomingDirection⟩
          have nextAligned :=
            (List.isChain_cons_cons.mp
              orthogonalParts.2).1
          rcases
              unitSubdividePolyline_firstDirection
                (rest := rest) nextAligned with
            ⟨after, tail, tailEquation,
              outgoingDirection⟩
          have segmentNoReversal :=
            unitSegmentPoints_hasNoImmediateReversal
              orthogonalParts.1
          rw [segmentEquation] at segmentNoReversal
          rw [tailEquation] at tailNoReversal
          have joined :=
            HasNoImmediateReversal.append_boundary
              segmentNoReversal
              tailNoReversal
              (by
                simpa [incomingDirection,
                  outgoingDirection] using
                    noReversalParts.1)
          rw [unitSubdividePolyline,
            segmentEquation, tailEquation,
            joinAtEndpoint]
          simpa [List.append_assoc] using joined

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

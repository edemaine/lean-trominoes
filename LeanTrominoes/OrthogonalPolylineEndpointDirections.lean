import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-!
# Endpoint directions of unit orthogonal polylines

The endpoint fans of a thickened route need only the first and final
cardinal directions of the underlying source polyline.  This file gives
total direction lookups, together with the genuine-direction certificates
available for every unit-step route containing at least one edge.
-/

namespace LeanTrominoes
namespace AxisDirection

/-- Any list with at least two entries can be split at its final edge. -/
theorem exists_eq_append_pair_of_length_ge_two
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

/-- Direction of the first listed edge of a polyline, with the invalid
fallback on lists containing fewer than two points. -/
def polylineFirstDirection : List Cell → AxisDirection
  | first :: second :: _ => between first second
  | _ => .invalid

/-- Direction of the final listed edge of a polyline, with the invalid
fallback on lists containing fewer than two points. -/
def polylineLastDirection (points : List Cell) : AxisDirection :=
  (polylineFirstDirection points.reverse).opposite

@[simp]
theorem polylineFirstDirection_cons_cons
    (first second : Cell) (rest : List Cell) :
    polylineFirstDirection (first :: second :: rest) =
      between first second := by
  rfl

/-- The opposite of a genuine cardinal direction is genuine. -/
theorem opposite_isGenuine
    {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    direction.opposite.IsGenuine := by
  cases direction <;>
    simp_all [IsGenuine, opposite]

/-- A unit cardinal step remains a unit cardinal step when traversed in
the opposite direction. -/
theorem IsUnitAxisStep.symm
    {source target : Cell}
    (unit : IsUnitAxisStep source target) :
    IsUnitAxisStep target source := by
  rcases unit with ⟨direction, genuine, rfl⟩
  refine ⟨direction.opposite,
    opposite_isGenuine genuine, ?_⟩
  cases direction <;>
    simp_all [IsGenuine, opposite, step, Cell.add]

/-- The first direction of a nondegenerate unit-step route is genuine. -/
theorem polylineFirstDirection_isGenuine
    {points : List Cell}
    (length : 2 ≤ points.length)
    (unitSteps : points.IsChain IsUnitAxisStep) :
    (polylineFirstDirection points).IsGenuine := by
  cases points with
  | nil =>
      simp at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp at length
      | cons second rest =>
          exact
            between_isGenuine_of_unitAxisStep
              (List.isChain_cons_cons.mp unitSteps).1

/-- The final direction of a nondegenerate unit-step route is genuine. -/
theorem polylineLastDirection_isGenuine
    {points : List Cell}
    (length : 2 ≤ points.length)
    (unitSteps : points.IsChain IsUnitAxisStep) :
    (polylineLastDirection points).IsGenuine := by
  have reversedLength :
      2 ≤ points.reverse.length := by
    simpa using length
  have reversedUnitSteps :
      points.reverse.IsChain IsUnitAxisStep := by
    rw [List.isChain_reverse]
    exact unitSteps.imp fun _ _ unit => unit.symm
  exact opposite_isGenuine
    (polylineFirstDirection_isGenuine
      reversedLength reversedUnitSteps)

/-- On an explicitly displayed final edge, the total final-direction lookup
returns that edge's forward direction. -/
@[simp]
theorem polylineLastDirection_append_pair
    (leading : List Cell) {before last : Cell}
    (unit : IsUnitAxisStep before last) :
    polylineLastDirection
        (leading ++ [before, last]) =
      between before last := by
  unfold polylineLastDirection
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append]
  change
    (between last before).opposite =
      between before last
  rw [between_reverse_eq_opposite
    (between_isGenuine_of_unitAxisStep unit)]
  simp

/-- Ordered unit subdivision preserves the first directed axis of every
nondegenerate orthogonal polyline. -/
theorem polylineFirstDirection_unitSubdividePolyline
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    polylineFirstDirection (unitSubdividePolyline points) =
      polylineFirstDirection points := by
  cases points with
  | nil =>
      simp at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp at length
      | cons second rest =>
          have aligned :=
            (List.isChain_cons_cons.mp orthogonal).1
          rcases unitSubdividePolyline_firstDirection aligned with
            ⟨after, tail, equation, direction⟩
          rw [equation]
          simpa [polylineFirstDirection] using direction

/-- Removing an initial point from a route containing at least three points
does not change its final directed axis. -/
theorem polylineLastDirection_cons_cons_cons
    (first second third : Cell) (rest : List Cell) :
    polylineLastDirection (first :: second :: third :: rest) =
      polylineLastDirection (second :: third :: rest) := by
  unfold polylineLastDirection
  rw [List.reverse_cons]
  congr 1
  cases reverseEquation :
      (second :: third :: rest).reverse with
  | nil =>
      have length :
          2 ≤ (second :: third :: rest).reverse.length := by
        simp
      simp [reverseEquation] at length
  | cons reversedFirst reversedRest =>
      cases reversedRest with
      | nil =>
          have length :
              2 ≤ (second :: third :: rest).reverse.length := by
            simp
          simp [reverseEquation] at length
      | cons reversedSecond reversedRest =>
          simp [polylineFirstDirection]

/-- Prepending any list to a route with at least two displayed points does
not change its final directed axis. -/
theorem polylineLastDirection_append_cons_cons
    (leading : List Cell) (first second : Cell) (rest : List Cell) :
    polylineLastDirection (leading ++ first :: second :: rest) =
      polylineLastDirection (first :: second :: rest) := by
  induction leading with
  | nil =>
      rfl
  | cons head tail induction =>
      rw [List.cons_append]
      cases tail with
      | nil =>
          simp only [List.nil_append]
          rw [polylineLastDirection_cons_cons_cons]
      | cons next tail =>
          cases tail with
          | nil =>
              simp only [List.cons_append, List.nil_append]
              rw [polylineLastDirection_cons_cons_cons]
              exact induction
          | cons third tail =>
              simp only [List.cons_append]
              rw [polylineLastDirection_cons_cons_cons]
              exact induction

/-- Joining a prefix to a nondegenerate suffix at their common endpoint
preserves the suffix's final directed axis. -/
theorem polylineLastDirection_joinAtEndpoint
    {first second : List Cell} {middle : Cell}
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (secondLength : 2 ≤ second.length) :
    polylineLastDirection (joinAtEndpoint first second) =
      polylineLastDirection second := by
  cases second with
  | nil =>
      simp at secondLength
  | cons secondFirst secondRest =>
      cases secondRest with
      | nil =>
          simp at secondLength
      | cons secondNext secondRest =>
          have secondFirstEq : secondFirst = middle := by
            simpa using Option.some.inj secondHead
          subst secondFirst
          cases first using List.reverseRecOn with
          | nil =>
              simp at firstLast
          | append_singleton leading last =>
              have lastEq : last = middle := by
                apply Option.some.inj
                simpa using firstLast
              subst last
              simp only [joinAtEndpoint, List.tail_cons,
                List.append_assoc]
              exact
                polylineLastDirection_append_cons_cons
                  leading middle secondNext secondRest

/-- Ordered unit subdivision preserves the final directed axis of every
nondegenerate orthogonal polyline. -/
theorem polylineLastDirection_unitSubdividePolyline
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    polylineLastDirection (unitSubdividePolyline points) =
      polylineLastDirection points := by
  induction points using List.twoStepInduction with
  | nil =>
      simp at length
  | singleton point =>
      simp at length
  | cons_cons first second rest _ induction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      cases rest with
      | nil =>
          rw [unitSubdividePolyline]
          rcases unitSegmentPoints_lastDirection parts.1 with
            ⟨leading, before, equation, direction⟩
          have segmentUnit :=
            unitSegmentPoints_unitSteps parts.1
          rw [equation] at segmentUnit
          have finalUnit :
              IsUnitAxisStep before second :=
            (List.isChain_append_cons_cons.mp segmentUnit).2.1
          rw [equation]
          simp only [unitSubdividePolyline_singleton,
            joinAtEndpoint, List.tail_cons, List.append_nil]
          rw [polylineLastDirection_append_pair
            leading finalUnit]
          rw [direction]
          change
            between first second =
              (between second first).opposite
          rw [between_reverse_eq_opposite
            (between_isGenuine_of_axisAligned parts.1),
            opposite_opposite]
      | cons third rest =>
          rw [unitSubdividePolyline]
          rw [polylineLastDirection_joinAtEndpoint
            (unitSegmentPoints_getLast? parts.1)
            (by
              simpa using unitSubdividePolyline_head?
                (points := second :: third :: rest)
                (by simp))
            (unitSubdividePolyline_length_ge_two
              (first := second) (second := third)
              (rest := rest) parts.2)]
          rw [induction second (by simp) parts.2]
          exact
            (polylineLastDirection_cons_cons_cons
              first second third rest).symm

end AxisDirection
end LeanTrominoes

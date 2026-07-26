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

end AxisDirection
end LeanTrominoes

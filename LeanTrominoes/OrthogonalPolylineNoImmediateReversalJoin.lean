import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-!
# Joining orthogonal routes without immediate reversals

Orthogonal route constructions are assembled from independently certified
pieces.  This file proves that joining two such pieces at a shared endpoint
preserves the absence of immediate reversals when their boundary directions
are compatible.
-/

namespace LeanTrominoes
namespace AxisDirection

/-- A list of length at least two exposes its final two entries. -/
private theorem exists_final_pair
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
              rcases induction
                  (by simp : 2 ≤ (second :: third :: rest).length) with
                ⟨leading, before, last, equation⟩
              exact
                ⟨first :: leading, before, last, by
                  simp [equation]⟩

/-- On an explicitly displayed final axis-aligned edge, the total
final-direction lookup returns that edge's forward direction. -/
private theorem polylineLastDirection_append_pair_axisAligned
    (leading : List Cell) {before last : Cell}
    (aligned : (GridSegment.mk before last).IsAxisAligned) :
    polylineLastDirection (leading ++ [before, last]) =
      between before last := by
  unfold polylineLastDirection
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append]
  change (between last before).opposite = between before last
  rw [between_reverse_eq_opposite
    (between_isGenuine_of_axisAligned aligned)]
  simp

/-- Joining two nondegenerate orthogonal routes at a shared endpoint
preserves the absence of immediate reversals when the newly adjacent
directions do not reverse one another. -/
theorem HasNoImmediateReversal.joinAtEndpoint_of_compatible
    {first second : List Cell} {middle : Cell}
    (firstNoReversal : HasNoImmediateReversal first)
    (secondNoReversal : HasNoImmediateReversal second)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (compatible :
      polylineFirstDirection second ≠
        (polylineLastDirection first).opposite) :
    HasNoImmediateReversal
      (LeanTrominoes.joinAtEndpoint first second) := by
  rcases exists_final_pair firstLength with
    ⟨leading, before, last, firstEquation⟩
  cases second with
  | nil =>
      simp at secondLength
  | cons secondFirst rest =>
      cases rest with
      | nil =>
          simp at secondLength
      | cons after rest =>
          have lastEqual : last = middle := by
            rw [firstEquation] at firstLast
            simpa using firstLast
          have firstEqual : secondFirst = middle := by
            simpa using secondHead
          subst last
          subst secondFirst
          have firstAligned :
              (GridSegment.mk before middle).IsAxisAligned := by
            rw [firstEquation] at firstOrthogonal
            exact
              (List.isChain_append_cons_cons.mp firstOrthogonal).2.1
          have boundary :
              between middle after ≠
                (between before middle).opposite := by
            simpa [polylineFirstDirection, firstEquation,
              polylineLastDirection_append_pair_axisAligned
                leading firstAligned] using compatible
          have joined :=
            HasNoImmediateReversal.append_boundary
              (by simpa [firstEquation] using firstNoReversal)
              secondNoReversal boundary
          have joined' :
              HasNoImmediateReversal
                ((leading ++ [before, middle]) ++ after :: rest) := by
            rw [List.append_assoc]
            exact joined
          unfold LeanTrominoes.joinAtEndpoint
          rw [firstEquation]
          simpa only [List.tail_cons] using joined'

end AxisDirection
end LeanTrominoes

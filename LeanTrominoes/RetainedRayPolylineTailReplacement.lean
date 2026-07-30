import LeanTrominoes.RetainedRayRasterization
import LeanTrominoes.OctilinearEmbeddedCNFIncidenceDrawing
import LeanTrominoes.OrthogonalPolylineTailReplacement

/-!
# Replacing tails of retained-ray polylines

The retained fixed-eight splice removes the old variable endpoint of a
source route and substitutes an orthogonal fan route beginning at the old
penultimate point.  Before rasterization, both the untouched source prefix
and the new suffix belong to the retained-ray vocabulary.  This file gives
`RetainedRayPolyline` the chain, prefix, join, and tail-replacement lemmas
needed to certify that combined route.
-/

namespace LeanTrominoes

/-- A list of length at least two has a genuine penultimate point, exposed
as the head of the reversed tail. -/
theorem exists_reverse_tail_head?_of_two_le_length
    {α : Type*} (route : List α)
    (routeLength : 2 ≤ route.length) :
    ∃ entrance, route.reverse.tail.head? = some entrance := by
  generalize reversedEq : route.reverse = reversed
  cases reversed with
  | nil =>
      have routeEq : route = [] := by
        simpa using congrArg List.reverse reversedEq
      subst route
      simp at routeLength
  | cons target rest =>
      cases rest with
      | nil =>
          have routeEq : route = [target] := by
            simpa using congrArg List.reverse reversedEq
          subst route
          simp at routeLength
      | cons entrance rest =>
          exact ⟨entrance, rfl⟩

/-- The reversed-tail view and the `dropLast` view expose the same
penultimate point. -/
theorem dropLast_getLast?_of_reverse_tail_head?
    {α : Type*} {route : List α} {entrance : α}
    (reverseTailHead :
      route.reverse.tail.head? = some entrance) :
    route.dropLast.getLast? = some entrance := by
  rw [← List.head?_reverse]
  simpa using reverseTailHead

namespace PeriodicEightOccurrenceSplit

/-- Segmentwise retained-ray membership is equivalently a chain condition
on consecutive listed points. -/
theorem retainedRayPolyline_iff_chain
    (points : List Cell) :
    RetainedRayPolyline points ↔
      points.IsChain fun first second =>
        RetainedRayVector (Cell.sub second first) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [RetainedRayPolyline, gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      constructor
      · intro retained
        rw [List.isChain_cons_cons]
        constructor
        · exact retained
            (GridSegment.mk first second)
            (by simp [gridPolylineSegments])
        · rw [← tailInduction second]
          intro segment segmentMember
          exact retained segment
            (by
              simp only [gridPolylineSegments,
                List.mem_cons]
              exact Or.inr segmentMember)
      · intro chain segment segmentMember
        rw [List.isChain_cons_cons] at chain
        simp only [gridPolylineSegments,
          List.mem_cons] at segmentMember
        rcases segmentMember with rfl | segmentMember
        · exact chain.1
        · exact (tailInduction second).mpr chain.2
            segment segmentMember

/-- Every orthogonal polyline uses only retained (cardinal) rays. -/
theorem RetainedRayPolyline.of_orthogonal
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    RetainedRayPolyline points := by
  exact RetainedRayPolyline.of_octilinear
    (OctilinearPolyline.of_orthogonal orthogonal)

/-- Removing the final listed point preserves retained-ray geometry. -/
theorem RetainedRayPolyline.dropLast
    {points : List Cell}
    (retained : RetainedRayPolyline points) :
    RetainedRayPolyline points.dropLast := by
  rw [retainedRayPolyline_iff_chain] at retained ⊢
  exact retained.dropLast

/-- Two retained-ray polylines remain retained when joined at their common
listed endpoint. -/
theorem RetainedRayPolyline.joinAtEndpoint
    {first second : List Cell} {middle : Cell}
    (firstRetained : RetainedRayPolyline first)
    (secondRetained : RetainedRayPolyline second)
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle) :
    RetainedRayPolyline
      (LeanTrominoes.joinAtEndpoint first second) := by
  rw [retainedRayPolyline_iff_chain] at firstRetained
  rw [retainedRayPolyline_iff_chain] at secondRetained
  rw [retainedRayPolyline_iff_chain]
  exact List.IsChain.joinAtEndpoint
    firstRetained secondRetained firstLast secondHead

/-- With a witnessed common penultimate point, tail replacement is exactly
the endpoint join of the old route without its last point and the
replacement. -/
theorem replacePolylineTail_eq_joinAtEndpoint_dropLast
    {α : Type*} (route replacement : List α)
    {middle : α}
    (routeEntrance :
      route.dropLast.getLast? = some middle)
    (replacementHead :
      replacement.head? = some middle) :
    replacePolylineTail route replacement =
      joinAtEndpoint route.dropLast replacement := by
  have routeDropEq :
      route.dropLast.dropLast ++ [middle] =
        route.dropLast :=
    List.dropLast_append_getLast? middle routeEntrance
  cases replacement with
  | nil =>
      simp at replacementHead
  | cons first rest =>
      have firstEq : first = middle :=
        Option.some.inj replacementHead
      subst first
      simp only [replacePolylineTail, replacePolylineHead,
        joinAtEndpoint, List.reverse_append,
        List.reverse_reverse, List.tail_cons]
      rw [← List.dropLast_reverse (l := route.reverse.tail)]
      rw [← List.dropLast_reverse (l := route.reverse)]
      rw [List.reverse_reverse]
      calc
        route.dropLast.dropLast ++ middle :: rest =
            (route.dropLast.dropLast ++ [middle]) ++ rest := by
              rw [List.append_assoc]
              rfl
        _ = route.dropLast ++ rest := by
              rw [routeDropEq]

/-- Replacing the last point of a retained route by a retained suffix
beginning at its old penultimate point preserves retained-ray geometry. -/
theorem RetainedRayPolyline.replaceTail
    {route replacement : List Cell} {middle : Cell}
    (routeRetained : RetainedRayPolyline route)
    (replacementRetained : RetainedRayPolyline replacement)
    (routeEntrance :
      route.dropLast.getLast? = some middle)
    (replacementHead : replacement.head? = some middle) :
    RetainedRayPolyline
      (LeanTrominoes.replacePolylineTail route replacement) := by
  rw [replacePolylineTail_eq_joinAtEndpoint_dropLast
    route replacement routeEntrance replacementHead]
  exact routeRetained.dropLast.joinAtEndpoint
    replacementRetained routeEntrance replacementHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes

import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation

/-!
# Aligned successful final direct routes

Every successful final direct-source choice represents an exact two-point
source route.  If its stored segment is axis-aligned, the represented source
route is therefore orthogonal.  This small bridge lets shared-endpoint source
planarity handle the aligned branch of mixed terminal-direction separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Axis alignment of a successful choice's represented segment makes the
corresponding original final source route orthogonal. -/
theorem
    retainedFinalDirectSourceRoute_orthogonal_of_sourceSegment_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (aligned : choice.sourceSegment.IsAxisAligned) :
    OrthogonalPolyline
      (finalCoordinatedSourceRoutes formula clauseIndex literalIndex) := by
  have routeLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).length = 2 := by
    have represents :=
      retainedFinalDirectSourceRouteChoice_representsFinalRoute
        formula clauseIndex literalIndex choice choiceLookup
    unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
    have routeEq :
        translatePolyline choice.origin
            (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
          finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex := by
      simpa only [finalCoordinatedSourceRoutes] using represents
    rw [← routeEq]
    simp only [translatePolyline, List.length_map,
      retainedDirectSourceLocalRouteAt_length]
  rcases List.length_eq_two.mp routeLength with
    ⟨start, finish, routeEq⟩
  have representedSegment :
      (⟨polylineLastEntrance
          (finalCoordinatedSourceRoutes formula clauseIndex literalIndex),
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).getLastD (0, 0)⟩ :
        GridSegment) = choice.sourceSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula clauseIndex literalIndex choice choiceLookup
  rw [routeEq] at representedSegment ⊢
  rw [orthogonalPolyline_iff_segments]
  intro segment segmentMember
  simp only [gridPolylineSegments, List.mem_singleton] at segmentMember
  subst segment
  simpa [polylineLastEntrance, List.getLastD_eq_getLast?]
    using representedSegment.symm ▸ aligned

end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalSourceHeadSeparationSupport
import LeanTrominoes.RetainedAngularFanFinalSourceRouteGeometry

/-! # Raw ordinary-fallback source-head separation -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- For a genuine non-singleton failed-direct route, its source point is
strictly separated from the coordinate rectangle of its final segment. -/
theorem
    finalCoordinatedFallbackSourceHead_finalSegmentRectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (prefixLengthNe :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).dropLast.length ≠ 1) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let sourcePoint :=
      PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance rawRoute, rawRoute.getLastD (0, 0)⟩
    ClosedGridRectanglesSeparated
      sourcePoint sourcePoint
      finalSegment.coordinateLower finalSegment.coordinateUpper := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let sourcePoint :=
    PositionedPeriodicCNF.canonicalClausePosition
      (finalCoordinatedPlacement formula) clause
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance rawRoute, rawRoute.getLastD (0, 0)⟩
  have rawLength : 2 ≤ rawRoute.length :=
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have rawLengthLarge : 3 ≤ rawRoute.length := by
    have prefixPositive : 0 < rawRoute.dropLast.length := by
      rw [List.length_dropLast]
      omega
    have prefixNotOne : rawRoute.dropLast.length ≠ 1 := by
      simpa [rawRoute] using prefixLengthNe
    have prefixLarge : 2 ≤ rawRoute.dropLast.length := by
      omega
    rw [List.length_dropLast] at prefixLarge
    omega
  have rawHead : rawRoute.head? = some sourcePoint := by
    simpa [rawRoute, sourcePoint] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).1
  have rawSimple : LocalIncidenceDrawing.RouteIsSimple rawRoute := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have rawOrthogonal : OrthogonalPolyline rawRoute := by
    simpa [rawRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have finalMember :
      finalSegment ∈ gridPolylineSegments rawRoute := by
    simpa [finalSegment] using finalGridSegment_mem rawRoute rawLength
  have finalMemberTail :
      finalSegment ∈ gridPolylineSegments rawRoute.tail := by
    simpa [finalSegment] using
      finalGridSegment_mem_tail_of_length_ge_three
        rawRoute rawLengthLarge
  have finalAligned : finalSegment.IsAxisAligned :=
    (orthogonalPolyline_iff_segments rawRoute).mp rawOrthogonal
      finalSegment finalMember
  have finalAvoidsHead : ¬finalSegment.Contains sourcePoint :=
    (rawSimple.tail_avoids_head rawHead).2
      finalSegment finalMemberTail finalAligned
  exact
    (finalSegment.coordinateRectangle_separated_point
      finalAligned finalAvoidsHead).symm

end PeriodicOrthocrossing
end LeanTrominoes

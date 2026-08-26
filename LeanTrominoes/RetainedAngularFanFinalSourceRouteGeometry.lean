/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation

/-! # Unscaled geometry of final copied-source routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- Every genuine final copied-source route is geometrically simple before
the source-clearance scale is applied. -/
theorem finalCoordinatedSourceRoute_isSimple
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  simpa only [finalCoordinatedSourceRoutes] using
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
      formula
      certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal
      retainedClausesNonempty
      (clause, clauseIndex)
      (by simpa only [finalCoordinatedSource] using clauseMember)
      (literal, literalIndex) literalMember

/-- Failure of the direct selector already makes the unscaled source route
orthogonal; the established scaled theorem reflects through its positive
uniform scale. -/
theorem finalCoordinatedFallbackSourceRoute_orthogonal
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
          formula clauseIndex literalIndex = none) :
    OrthogonalPolyline
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex) := by
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  have scaledOrthogonal :
      OrthogonalPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor route) := by
    simpa [route] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  change OrthogonalPolyline route
  rw [orthogonalPolyline_iff_segments]
  intro segment segmentMember
  have scaledMember :
      segment.scale retainedAngularFanSourceClearanceFactor ∈
        gridPolylineSegments
          (scalePolyline retainedAngularFanSourceClearanceFactor route) := by
    rw [gridPolylineSegments_scalePolyline]
    exact List.mem_map.mpr ⟨segment, segmentMember, rfl⟩
  have scaledAligned :=
    (orthogonalPolyline_iff_segments _).mp scaledOrthogonal
      (segment.scale retainedAngularFanSourceClearanceFactor)
      scaledMember
  exact
    (GridSegment.isAxisAligned_scale_iff
      (by
        exact_mod_cast retainedAngularFanSourceClearanceFactor_pos)
      segment).mp scaledAligned

end PeriodicOrthocrossing
end LeanTrominoes

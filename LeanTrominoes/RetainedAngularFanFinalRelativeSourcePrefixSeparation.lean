import LeanTrominoes.RetainedFinalSourceRouteOtherTranslatedVertexSeparation
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationOrdering

/-!
# Relative separation of final retained source prefixes

Before the final angular-fan replacement, every copied-source route is a
retained route of the periodically planar source drawing.  Relative source
separation may allow two occurrences to share their variable endpoint.  Once
that final point is deleted, simplicity and separation of the clause heads
upgrade the certificate to strict contact-free separation.  This module
records that fact before and after the full source-first refinement.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicEightOccurrenceSplit

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Clause representatives in the retained source fundamental square cannot
coincide after a nonzero semantic period translation. -/
theorem finalCoordinatedCanonicalClausePositions_ne_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) firstClause ≠
      Cell.add
        (PositionedPeriodicCNF.canonicalClausePosition
          (finalCoordinatedPlacement formula) secondClause)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  have firstPositionMember :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstClause ∈
        PositionedPeriodicCNF.incidenceVertexPositions
          source placement := by
    rw [PositionedPeriodicCNF.incidenceVertexPositions]
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_map.mpr
        ⟨firstClause, List.fst_mem_of_mem_zipIdx firstClauseMember, rfl⟩
  have secondPositionMember :
      PositionedPeriodicCNF.canonicalClausePosition
          placement secondClause ∈
        PositionedPeriodicCNF.incidenceVertexPositions
          source placement := by
    rw [PositionedPeriodicCNF.incidenceVertexPositions]
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_map.mpr
        ⟨secondClause, List.fst_mem_of_mem_zipIdx secondClauseMember, rfl⟩
  have firstBounds :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_inSquare
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal retainedClausesNonempty
      (PositionedPeriodicCNF.canonicalClausePosition
        placement firstClause)
      (by
        simpa [source, placement, finalCoordinatedSource,
          finalCoordinatedPlacement] using firstPositionMember)
  have secondBounds :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_inSquare
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal retainedClausesNonempty
      (PositionedPeriodicCNF.canonicalClausePosition
        placement secondClause)
      (by
        simpa [source, placement, finalCoordinatedSource,
          finalCoordinatedPlacement] using secondPositionMember)
  have periodPositive : 0 < placement.period := by
    simpa [placement, finalCoordinatedPlacement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  exact
    PeriodicVariablePlacement.position_ne_add_translation_of_inSquare_of_nonzero
      placement periodPositive
      (by
        simpa [placement, finalCoordinatedPlacement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement] using firstBounds)
      (by
        simpa [placement, finalCoordinatedPlacement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement] using secondBounds)
      relativeTranslate relativeTranslateNonzero

/-- Complete retained source routes satisfy ordinary endpoint-only
separation at every nonzero relative shift. -/
theorem finalCoordinatedSourceRoutes_avoid_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesAvoidEachOther
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have sourceRelative :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_relativeAvoidEachOther
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal retainedClausesNonempty
  have sourceCoordinate :=
    @PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther.coordinate
      (WrappedPeriodicPlanarSATVariable Variable)
      (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
        Variable inferInstance)
      _ _ _ sourceRelative
  have occurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate) := by
    intro occurrencesEqual
    apply relativeTranslateNonzero
    exact (congrArg Prod.snd occurrencesEqual).symm
  simpa [finalCoordinatedSource, finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes, translatePolyline] using
    sourceCoordinate
      firstClause firstClauseIndex firstClauseMember
      firstLiteral firstLiteralIndex firstLiteralMember
      secondClause secondClauseIndex secondClauseMember
      secondLiteral secondLiteralIndex secondLiteralMember
      relativeTranslate occurrencesDifferent

/-- At a nonzero relative period shift, the final-point-deleted retained raw
source routes are strictly contact-free.  Possible coincidence of their
variable endpoints is harmless because both endpoints have been deleted. -/
theorem
    finalCoordinatedSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex).dropLast
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)).dropLast := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let firstRoute := routes firstClauseIndex firstLiteralIndex
  let secondRoute := routes secondClauseIndex secondLiteralIndex
  let translatedSecondRoute :=
    translatePolyline (placement.translation relativeTranslate) secondRoute
  have occurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate) := by
    intro occurrencesEqual
    apply relativeTranslateNonzero
    exact (congrArg Prod.snd occurrencesEqual).symm
  have sourceRelative :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_relativeAvoidEachOther
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal retainedClausesNonempty
  have sourceCoordinate :=
    @PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther.coordinate
      (WrappedPeriodicPlanarSATVariable Variable)
      (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
        Variable inferInstance)
      _ _ _ sourceRelative
  have rawAvoid : RoutesAvoidEachOther firstRoute translatedSecondRoute := by
    simpa [source, placement, routes, firstRoute, secondRoute,
      translatedSecondRoute, finalCoordinatedSource,
      finalCoordinatedPlacement, finalCoordinatedSourceRoutes,
      translatePolyline] using
      sourceCoordinate
        firstClause firstClauseIndex firstClauseMember
        firstLiteral firstLiteralIndex firstLiteralMember
        secondClause secondClauseIndex secondClauseMember
        secondLiteral secondLiteralIndex secondLiteralMember
        relativeTranslate occurrencesDifferent
  have firstNodup : firstRoute.Nodup := by
    simpa [source, routes, firstRoute,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal retainedClausesNonempty
        (firstClause, firstClauseIndex)
        (by simpa [source, finalCoordinatedSource] using firstClauseMember)
        (firstLiteral, firstLiteralIndex) firstLiteralMember).1
  have secondNodup : secondRoute.Nodup := by
    simpa [source, routes, secondRoute,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal retainedClausesNonempty
        (secondClause, secondClauseIndex)
        (by simpa [source, finalCoordinatedSource] using secondClauseMember)
        (secondLiteral, secondLiteralIndex) secondLiteralMember).1
  have translatedSecondNodup : translatedSecondRoute.Nodup := by
    unfold translatedSecondRoute translatePolyline
    exact secondNodup.map
      (Cell.add_left_injective (placement.translation relativeTranslate))
  have firstHead :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember).1
  have secondHead :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember).1
  have translatedSecondHead :
      translatedSecondRoute.head? =
        some
          (Cell.add (placement.translation relativeTranslate)
            (PositionedPeriodicCNF.canonicalClausePosition
              placement secondClause)) := by
    simp [translatedSecondRoute, translatePolyline,
      secondRoute, routes, placement, secondHead]
  have headsDifferent : firstRoute.head? ≠ translatedSecondRoute.head? := by
    have clausePositionsDifferent :=
      finalCoordinatedCanonicalClausePositions_ne_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        relativeTranslate relativeTranslateNonzero
    intro headsEqual
    rw [show firstRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement firstClause) by
          simpa [firstRoute, routes, placement] using firstHead,
      translatedSecondHead] at headsEqual
    apply clausePositionsDifferent
    have pointsEqual := Option.some.inj headsEqual
    simpa [placement, Cell.add, add_comm] using pointsEqual
  exact
    routesStrictlyAvoidEachOther_dropLast_of_avoid_of_nodup_of_heads_ne
      rawAvoid firstNodup translatedSecondNodup headsDifferent

/-- The prefix certificate after the complete source-first refinement used
by all final angular-fan routes. -/
theorem
    finalCoordinatedFullyScaledSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let factor : Nat :=
      retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor
    RoutesStrictlyAvoidEachOther
      (scalePolyline factor
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex)).dropLast
      (translatePolyline
        (((finalCoordinatedPlacement formula).scale factor).translation
          relativeTranslate)
        (scalePolyline factor
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))).dropLast := by
  dsimp only
  have unscaled :=
    finalCoordinatedSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      relativeTranslate relativeTranslateNonzero
  have scaled :=
    unscaled.scalePolyline
      (factor :=
        ((retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor : Nat) : Int))
      (by
        norm_num [retainedTerminalFanTotalRefinement_eq,
          retainedAngularFanSourceClearanceFactor_eq])
  rw [← scalePolyline_dropLast_eq,
    ← scalePolyline_dropLast_eq] at scaled
  rw [scalePolyline_translatePolyline] at scaled
  simpa only [PeriodicVariablePlacement.translation_scale] using scaled

end PeriodicOrthocrossing
end LeanTrominoes

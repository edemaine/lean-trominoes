/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalSourceScaledExpandedBounds
import LeanTrominoes.RetainedAngularFanSourceScaledRouteRadiusBounds
import LeanTrominoes.RetainedAngularFanSourceSpliceRouteRadiusBounds

/-!
# Variable-centered radius bounds for the final source-scaled routes

The strict one-cell margin of the retained planar-SAT source survives the
source-clearance scale and pays for the fixed local occurrence fan.  The
appended implication-cycle routes are uniformly local: before the final
factor-eight refinement, both a route point and its literal endpoint lie in
the same `12 × 12` macrocell square.  Together these facts put every physical
route point within one public period of its canonical literal endpoint, and
hence every rebased route within one period of its variable representative.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicEightOccurrenceSplitPositioned

/-- Every point of a genuine unrefined implication-cycle route is within
coordinate radius twelve of that incidence's canonical literal endpoint. -/
theorem allCycleRoute_point_withinCanonicalLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        allCycleRoutes source sourcePlacement
          cycleIndex literalIndex) :
    WithinCoordinateRadius 12
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (placement sourcePlacement) clause literal)
      point := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      _localClauseMember⟩
  have pointBounded :=
    positionedCycleRoutes_inClosedGridRectangle
      sourcePlacement metadata.atom metadata.localClauseIndex
      literalIndex
      (by simpa [allCycleRoutes, metadataLookup] using pointMember)
  have endpoints :=
    allCycleRoutes_physicalRoutesMatch
      source sourcePlacement
      clause cycleIndex clauseMember
      literal literalIndex literalMember
  have endpointMember :
      (placement sourcePlacement).literalPosition literal ∈
        allCycleRoutes source sourcePlacement
          cycleIndex literalIndex :=
    mem_of_getLast?_eq_some endpoints.2
  have endpointBounded :=
    positionedCycleRoutes_inClosedGridRectangle
      sourcePlacement metadata.atom metadata.localClauseIndex
      literalIndex
      (by simpa [allCycleRoutes, metadataLookup] using endpointMember)
  have anchorZero :=
    allCycleClauses_clauseAnchor_eq_zero
      source sourcePlacement clauseMember
  have offsetZero :=
    allCycleClauses_literal_offset_eq_zero
      source sourcePlacement clauseMember literalMember
  have canonicalEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (placement sourcePlacement) clause literal =
        (placement sourcePlacement).literalPosition literal := by
    simp [PositionedPeriodicCNF.canonicalLiteralPosition,
      PeriodicVariablePlacement.literalPosition,
      anchorZero, offsetZero,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub,
      Cell.scale]
  rw [canonicalEq]
  simp only [positionedCycleRouteLower,
    positionedCycleRouteUpper, InClosedGridRectangle,
    Cell.add] at pointBounded endpointBounded
  constructor <;> omega

/-- The factor-eight physical implication routes remain within radius 96 of
their correspondingly refined canonical literal endpoints. -/
theorem scaledAllCycleRoute_point_withinCanonicalLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes source sourcePlacement
            cycleIndex literalIndex)) :
    WithinCoordinateRadius 96
      (PositionedPeriodicCNF.canonicalLiteralPosition
        ((placement sourcePlacement).scale
          retainedTerminalFanRoutingRefinement)
        (clause.scale retainedTerminalFanRoutingRefinement)
        literal)
      point := by
  rw [scalePolyline, List.mem_map] at pointMember
  rcases pointMember with ⟨localPoint, localPointMember, rfl⟩
  have bounded :=
    (allCycleRoute_point_withinCanonicalLiteralRadius
      source sourcePlacement clauseMember literalMember
      localPointMember).scale retainedTerminalFanRoutingRefinement
  simpa only [
    PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
    retainedTerminalFanRoutingRefinement] using bounded

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

/-- Every physical route point of the final source-scaled fixed-eight family
lies within one less than the public placement period of its canonical
literal endpoint. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPredPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) :
    WithinCoordinateRadius
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period - 1)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula)
        clause literal)
      point := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let scaledSource :=
    source.scale retainedAngularFanSourceClearanceFactor
  let scaledPlacement :=
    placement.scale retainedAngularFanSourceClearanceFactor
  let scaledRoutes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor routes
  let order := angularOccurrenceOrder scaledSource.erase scaledRoutes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder scaledSource.erase order
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have sourceBounds :=
    retainedDeduplicatedGaugedWrappedDrawingIncidenceRoutes_withinVariablePredPeriod
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
  have publicPeriodEq :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq
      formula
  have sourcePeriodPositive :
      0 < (finalCoordinatedPlacement formula).period := by
    simpa [finalCoordinatedPlacement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have clauseIndexEqual : baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement = clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have baseLiteralMember :
      (literal, literalIndex) ∈ baseClause.literals.zipIdx := by
    simpa using literalMember
  change
    point ∈
      retainedAngularFanSplicedIncidenceRoutes
        scaledSource scaledPlacement scaledRoutes
        baseIndex literalIndex at pointMember
  by_cases occurrenceIndex :
      baseIndex <
        (occurrenceClauses scaledSource occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        scaledSource scaledPlacement order taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    rcases occurrenceClauseMetadata_lookup
        scaledSource occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        scaledSourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have scaledSourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          scaledSource.clauses.zipIdx := by
      simpa [metadataIndex] using scaledSourceClauseMember
    have copiedClauseEqual :
        baseClause =
          occurrenceClause occurrencePorts baseIndex
            metadata.sourceClause := by
      calc
        baseClause = metadata.clause := metadataClauseEqual.symm
        _ = occurrenceClause occurrencePorts metadata.clauseIndex
              metadata.sourceClause := metadataClauseDefinition
        _ = occurrenceClause occurrencePorts baseIndex
              metadata.sourceClause := by rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual baseLiteralMember with
      ⟨sourceLiteral, scaledSourceLiteralMember,
        copiedLiteralEqual⟩
    have scaledSourceClauseMemberForRoute :=
      scaledSourceClauseMemberAt
    change
      (metadata.sourceClause, baseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx
      at scaledSourceClauseMemberAt
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at scaledSourceClauseMemberAt
    rcases List.mem_map.mp scaledSourceClauseMemberAt with
      ⟨taggedSourceClause, sourceClauseMember,
        scaledSourceClauseEqual⟩
    rcases taggedSourceClause with
      ⟨sourceClause, sourceClauseIndex⟩
    have sourceClauseIndexEqual : sourceClauseIndex = baseIndex :=
      congrArg Prod.snd scaledSourceClauseEqual
    have sourceClauseScaleEqual :
        sourceClause.scale retainedAngularFanSourceClearanceFactor =
          metadata.sourceClause :=
      congrArg Prod.fst scaledSourceClauseEqual
    subst sourceClauseIndex
    have sourceLiteralMember :
        (sourceLiteral, literalIndex) ∈
          sourceClause.literals.zipIdx := by
      simpa only [← sourceClauseScaleEqual,
        PositionedPeriodicClause.scale_literals] using
        scaledSourceLiteralMember
    rw [
      retainedAngularFanSplicedIncidenceRoutes_occurrence
        scaledSource scaledPlacement scaledRoutes
        baseIndex literalIndex
        (by simpa [occurrencePorts] using occurrenceIndex),
      retainedAngularFanSplicedOccurrenceRoutes_of_members
        scaledSource scaledPlacement scaledRoutes
        scaledSourceClauseMemberForRoute
        scaledSourceLiteralMember] at pointMember
    change
      point ∈
        retainedAngularFanSplicedOccurrenceRoute
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes formula))
          metadata.sourceClause sourceLiteral
          baseIndex literalIndex at pointMember
    rw [← sourceClauseScaleEqual] at pointMember
    let terminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula baseIndex literalIndex))
    have classified :
        retainedTerminalDirectionClassify
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula baseIndex literalIndex)) =
          some terminal := by
      exact
        finalCoordinatedSourceRoute_classified
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember
    have rawRouteBounded :
        ∀ routePoint ∈
            finalCoordinatedSourceRoutes formula
              baseIndex literalIndex,
          WithinCoordinateRadius
            ((finalCoordinatedPlacement formula).period - 1)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (finalCoordinatedPlacement formula)
              sourceClause sourceLiteral)
            routePoint := by
      intro routePoint routePointMember
      exact
        PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius.rawRoutePointsWithinCanonicalLiteralRadius
          (by simpa [finalCoordinatedSource,
            finalCoordinatedPlacement,
            finalCoordinatedSourceRoutes] using sourceBounds)
          sourceClauseMember sourceLiteralMember routePointMember
    have bounded :=
      retainedAngularFanSourceScaledSplicedOccurrenceRoute_point_withinCopiedLiteralRadius
        retainedAngularFanSourceClearanceFactor_pos
        (finalCoordinatedSource formula)
        (finalCoordinatedPlacement formula)
        (finalCoordinatedSourceRoutes formula)
        sourceClauseMember sourceLiteralMember terminal
        classified
        (finalCoordinatedSourceRoutes_length_ge_two
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
        (finalCoordinatedSourceRoutes_retainedRay
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
        rawRouteBounded pointMember
    have radiusLe :
        (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor) *
              ((finalCoordinatedPlacement formula).period - 1) +
            345 ≤
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).period - 1 := by
      rw [publicPeriodEq]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedAngularFanSourceClearanceFactor]
      omega
    have finalBounded := bounded.mono radiusLe
    simpa only [copiedClauseEqual, copiedLiteralEqual,
      ← sourceClauseScaleEqual,
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
      retainedAngularFanSourceScaledRefinedPlacement,
      retainedAngularFanRefinedPlacement,
      occurrencePorts, order, scaledSource, scaledRoutes,
      source, placement, routes,
      finalCoordinatedPlacement,
      scaledPlacement,
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
      using finalBounded
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        scaledSource scaledPlacement occurrencePorts
        taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    let cycleIndex :=
      baseIndex - (occurrenceClauses scaledSource occurrencePorts).length
    have clauseIndexDecomposition :
        baseIndex =
          (occurrenceClauses scaledSource occurrencePorts).length +
            cycleIndex := by
      dsimp only [cycleIndex]
      omega
    rw [clauseIndexDecomposition,
      retainedAngularFanSplicedIncidenceRoutes_cycle]
      at pointMember
    have bounded :=
      scaledAllCycleRoute_point_withinCanonicalLiteralRadius
        scaledSource scaledPlacement
        (by simpa only [cycleIndex] using cycleClauseMember)
        baseLiteralMember pointMember
    have radiusLe :
        96 ≤
          (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).period - 1 := by
      rw [publicPeriodEq]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedAngularFanSourceClearanceFactor]
      omega
    exact bounded.mono radiusLe

/-- One-period corollary of the strict source-scaled fixed-eight radius
bound. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) :
    WithinCoordinateRadius
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula)
        clause literal)
      point := by
  exact
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPredPeriod
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember pointMember).mono
        (Nat.sub_le _ _)

/-- The final source-scaled fixed-eight family has the complete strict
rebased variable-radius certificate. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_withinVariablePredPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period - 1)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula) := by
  apply
    PositionedPeriodicCNF.rebasedIncidenceRoutesWithinVariableRadius_of_rawRoutePointsWithinCanonicalLiteralRadius
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember point pointMember
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPredPeriod
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember pointMember

/-- The final source-scaled fixed-eight family has the complete rebased
one-period variable-radius certificate. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula) := by
  apply
    PositionedPeriodicCNF.rebasedIncidenceRoutesWithinVariableRadius_of_rawRoutePointsWithinCanonicalLiteralRadius
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember point pointMember
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_rawRoutePoint_withinCanonicalLiteralPeriod
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember pointMember

end PeriodicOrthocrossing
end LeanTrominoes

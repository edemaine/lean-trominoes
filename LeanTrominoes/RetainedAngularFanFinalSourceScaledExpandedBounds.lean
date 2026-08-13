/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCycleExpandedBounds
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity
import LeanTrominoes.RetainedAngularFanSourceSpliceExpandedBounds

/-!
# Expanded-period bounds for the final source-scaled fixed-eight routes

The raw retained planar-SAT routes already lie in the open neighboring-period
square.  Source-first scaling creates enough strict margin to insert and
rasterize the fixed angular fan.  This module first specializes that generic
fact to the final retained source, then combines copied occurrences with the
appended implication-cycle routes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 4000000

/-- Every point of a genuine route in the final retained source lies in the
open neighboring-period square before source-clearance scaling. -/
theorem finalCoordinatedSourceRoutes_point_inExpanded
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
    {point : Cell}
    (pointMember :
      point ∈ finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex) :
    let sourcePeriod : Int :=
      (finalCoordinatedPlacement formula).period;
    -sourcePeriod < point.1 ∧
      point.1 < 2 * sourcePeriod ∧
      -sourcePeriod < point.2 ∧
      point.2 < 2 * sourcePeriod := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have bounded :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutePoint_inExpandedSquare
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal retainedClausesNonempty
      (clause, clauseIndex) (by
        simpa only [finalCoordinatedSource] using clauseMember)
      (literal, literalIndex) literalMember pointMember
  unfold PeriodicGridDrawing.PositionInExpandedSquare at bounded
  simp only [
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing,
    PositionedPeriodicCNF.incidenceDrawing,
    PeriodicGridDrawing.gridSize] at bounded
  have periodPositive :
      0 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have gridSizeEq :
      Nat.pred
            (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              formula).period +
          1 =
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    simpa [Nat.succ_eq_add_one] using
      Nat.succ_pred_eq_of_pos periodPositive
  simp only [gridSizeEq] at bounded
  simpa only [finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes] using bounded

/-- The public fixed-eight placement period is the raw retained-source
period multiplied by the source-clearance and complete fan refinements. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period =
      (retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor) *
          (finalCoordinatedPlacement formula).period := by
  simp only [
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,
    retainedAngularFanRefinedPlacement,
    PeriodicEightOccurrenceSplitPositioned.placement,
    PeriodicVariablePlacement.scale_period,
    finalCoordinatedPlacement,
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period]
  norm_num [
    retainedTerminalFanTotalRefinement_eq,
    retainedTerminalFanRoutingRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    retainedAngularFanSourceClearanceFactor]
  change
    8 *
        (36 *
          (4 *
            (wrappedDrawingPeriodicPlanarSATPlacement formula).period)) =
      1152 *
        (wrappedDrawingPeriodicPlanarSATPlacement formula).period
  ring

/-- Every point of a copied occurrence route built from the final retained
source lies in the open neighboring-period square after source-first scaling
and terminal-fan refinement. -/
theorem retainedFinalSourceScaledSplicedOccurrenceRoute_point_inExpanded
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
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanSplicedOccurrenceRoute
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes formula))
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) :
    let refinedPeriod : Int :=
      (retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor) *
          (finalCoordinatedPlacement formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  let terminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex))
  apply
    retainedAngularFanSourceScaledSplicedOccurrenceRoute_point_inExpanded
      retainedAngularFanSourceClearanceFactor_pos
      (by
        norm_num [retainedTerminalFanTotalRefinement_eq,
          retainedAngularFanSourceClearanceFactor])
      (finalCoordinatedSource formula)
      (finalCoordinatedPlacement formula)
      (finalCoordinatedSourceRoutes formula)
      clauseMember literalMember terminal
  · exact
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · exact
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · exact
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · exact
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
  · intro routePoint routePointMember
    exact
      finalCoordinatedSourceRoutes_point_inExpanded
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        routePointMember
  · exact pointMember

/-- Every point of every genuine route in the final source-scaled fixed-eight
drawing lies in the open neighboring-period square of its public refined
placement. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_point_inExpanded
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
    let refinedPeriod : Int :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
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
  have publicPeriodEq :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_eq
      formula
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
        _copiedLiteralEqual⟩
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
    rcases taggedSourceClause with ⟨sourceClause, sourceClauseIndex⟩
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
    have bounded :=
      retainedFinalSourceScaledSplicedOccurrenceRoute_point_inExpanded
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember
        sourceLiteralMember
        pointMember
    simpa only [publicPeriodEq, Nat.cast_mul] using bounded
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
      retainedFinalSourceScaledAllCycleRoute_point_inExpanded
        formula
        (by simpa only [cycleIndex] using cycleClauseMember)
        literalIndex pointMember
    simpa only [publicPeriodEq, Nat.cast_mul] using bounded

end PeriodicOrthocrossing
end LeanTrominoes

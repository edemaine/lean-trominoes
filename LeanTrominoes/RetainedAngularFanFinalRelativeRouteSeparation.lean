/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalPublicRouteSeparation
import LeanTrominoes.RetainedAngularFanFinalNormalizedDrawing
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationOrdering

/-!
# Relative separation of the complete final fixed-eight route family

The total family has three geometric pair types: copied source versus copied
source, copied source versus an appended Figure 7 cycle, and cycle versus
cycle.  The latter two are now periodic theorems.  This module packages them
with an explicit premise for the one remaining copied-source pair type and
then transports the resulting certificate through loop erasure to the final
normalized drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The remaining relative-separation obligation restricted to two genuine
copied-source incidences of the public coordinated route family. -/
def RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ firstClause firstClauseIndex,
    (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx →
    ∀ firstLiteral firstLiteralIndex,
      (firstLiteral, firstLiteralIndex) ∈
          firstClause.literals.zipIdx →
      ∀ secondClause secondClauseIndex,
        (secondClause, secondClauseIndex) ∈
            (finalCoordinatedSource formula).clauses.zipIdx →
        ∀ secondLiteral secondLiteralIndex,
          (secondLiteral, secondLiteralIndex) ∈
              secondClause.literals.zipIdx →
          ∀ relativeTranslate,
            ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
                ((secondClauseIndex, secondLiteralIndex),
                  relativeTranslate) →
              RoutesAvoidEachOther
                (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
                  formula firstClauseIndex firstLiteralIndex)
                (translatePolyline
                  ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                    formula).translation relativeTranslate)
                  (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
                    formula secondClauseIndex secondLiteralIndex))

/-- The reverse mixed branch, obtained from source--cycle separation at the
opposite period shift and then translating both routes back. -/
theorem retainedFinalSourceScaledAllCycleRoute_avoids_translatedCoordinatedSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {sourceClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {sourceLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈ sourceClause.literals.zipIdx)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈ cycleClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    RoutesAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex))
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula sourceClauseIndex sourceLiteralIndex)) := by
  have backwards :=
    retainedFinalCoordinatedSourceRoute_avoids_translatedAllCycleRoute
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember
      cycleClauseMember cycleLiteralMember (Cell.neg relativeTranslate)
  have shifted :=
    (routesAvoidEachOther_comm backwards).translate
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate)
  have shiftCancel :
      Cell.add
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).translation (Cell.neg relativeTranslate))
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).translation relativeTranslate) =
        (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [PeriodicVariablePlacement.translation,
      Cell.neg, Cell.add, Cell.sub, Cell.scale]
  rw [translatePolyline_add, shiftCancel,
    translatePolyline_zero] at shifted
  exact shifted

/-- Figure 7 cycle routes are relatively separated: the zero shift uses the
within-cell theorem, while every nonzero shift uses strict periodic
separation. -/
theorem retainedFinalSourceScaledAllCycleRoutes_coordinateRelativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (zeroShiftDistinct :
      relativeTranslate = (0, 0) →
        firstCycleIndex ≠ secondCycleIndex ∨
          firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          firstCycleIndex firstLiteralIndex))
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            secondCycleIndex secondLiteralIndex))) := by
  by_cases translateZero : relativeTranslate = (0, 0)
  · subst relativeTranslate
    have translationZero :
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation (0, 0) = (0, 0) := by
      simp [PeriodicVariablePlacement.translation, Cell.scale]
    rw [translationZero, translatePolyline_zero]
    exact
      retainedFinalSourceScaledAllCycleRoutes_avoidEachOther
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember (zeroShiftDistinct rfl)
  · exact
      (retainedFinalSourceScaledAllCycleRoutes_strictlyAvoidEachOther_of_nonzero
        formula firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate translateZero).toRoutesAvoidEachOther

/-- Relative separation of copied source routes, supplied as the sole
remaining premise, combines with the completed periodic cycle branches to
separate the entire coordinated fixed-eight incidence family. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_coordinateRelativeAvoidEachOther_of_copiedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (copiedSourceRelative :
      RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula) :
    PositionedPeriodicCNF.CoordinateRelativeIncidenceRoutesAvoidEachOther
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula) := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order := angularOccurrenceOrder source.erase routes
  let occurrencePorts := occurrencePortsOfAngularOrder source.erase order
  let boundary := (occurrenceClauses source occurrencePorts).length
  intro firstClause firstClauseIndex firstClauseMember
    firstLiteral firstLiteralIndex firstLiteralMember
    secondClause secondClauseIndex secondClauseMember
    secondLiteral secondLiteralIndex secondLiteralMember
    relativeTranslate occurrencesDifferent
  rcases finalCoordinatedIncidence_unscale
      formula firstClauseMember firstLiteralMember with
    ⟨firstBaseClause, firstBaseClauseMember,
      firstBaseLiteralMember⟩
  rcases finalCoordinatedIncidence_unscale
      formula secondClauseMember secondLiteralMember with
    ⟨secondBaseClause, secondBaseClauseMember,
      secondBaseLiteralMember⟩
  by_cases firstOccurrence : firstClauseIndex < boundary
  · rcases rawCoordinatedSourceIncidence_of_occurrence
        formula
        (by simpa [source, placement, routes, order, occurrencePorts] using
          firstBaseClauseMember)
        firstBaseLiteralMember
        (by simpa [source, routes, order, occurrencePorts, boundary] using
          firstOccurrence) with
      ⟨firstSourceClause, firstSourceLiteral,
        firstSourceClauseMember, firstSourceLiteralMember⟩
    by_cases secondOccurrence : secondClauseIndex < boundary
    · rcases rawCoordinatedSourceIncidence_of_occurrence
          formula
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          secondBaseLiteralMember
          (by simpa [source, routes, order, occurrencePorts, boundary] using
            secondOccurrence) with
        ⟨secondSourceClause, secondSourceLiteral,
          secondSourceClauseMember, secondSourceLiteralMember⟩
      exact
        copiedSourceRelative
          firstSourceClause firstClauseIndex firstSourceClauseMember
          firstSourceLiteral firstLiteralIndex firstSourceLiteralMember
          secondSourceClause secondClauseIndex secondSourceClauseMember
          secondSourceLiteral secondLiteralIndex secondSourceLiteralMember
          relativeTranslate occurrencesDifferent
    · have secondCycleClauseMember :=
        cycleClauseMember_of_formula_member
          source placement occurrencePorts
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          (by simpa [boundary] using secondOccurrence)
      have secondDecomposition :
          secondClauseIndex =
            boundary + (secondClauseIndex - boundary) := by omega
      rw [secondDecomposition,
        retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute]
      simpa only [source, placement, routes, order, occurrencePorts,
        boundary, translatePolyline] using
        retainedFinalCoordinatedSourceRoute_avoids_translatedAllCycleRoute
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstSourceClauseMember firstSourceLiteralMember
          secondCycleClauseMember secondBaseLiteralMember
          relativeTranslate
  · have firstCycleClauseMember :=
      cycleClauseMember_of_formula_member
        source placement occurrencePorts
        (by simpa [source, placement, routes, order, occurrencePorts] using
          firstBaseClauseMember)
        (by simpa [boundary] using firstOccurrence)
    have firstDecomposition :
        firstClauseIndex =
          boundary + (firstClauseIndex - boundary) := by omega
    by_cases secondOccurrence : secondClauseIndex < boundary
    · rcases rawCoordinatedSourceIncidence_of_occurrence
          formula
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          secondBaseLiteralMember
          (by simpa [source, routes, order, occurrencePorts, boundary] using
            secondOccurrence) with
        ⟨secondSourceClause, secondSourceLiteral,
          secondSourceClauseMember, secondSourceLiteralMember⟩
      rw [firstDecomposition,
        retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute]
      exact
        retainedFinalSourceScaledAllCycleRoute_avoids_translatedCoordinatedSourceRoute
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondSourceClauseMember secondSourceLiteralMember
          firstCycleClauseMember firstBaseLiteralMember
          relativeTranslate
    · have secondCycleClauseMember :=
        cycleClauseMember_of_formula_member
          source placement occurrencePorts
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          (by simpa [boundary] using secondOccurrence)
      have secondDecomposition :
          secondClauseIndex =
            boundary + (secondClauseIndex - boundary) := by omega
      rw [firstDecomposition, secondDecomposition,
        retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute,
        retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute]
      apply
        retainedFinalSourceScaledAllCycleRoutes_coordinateRelativeAvoidEachOther
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstCycleClauseMember secondCycleClauseMember
          firstBaseLiteralMember secondBaseLiteralMember
          relativeTranslate
      intro translateZero
      have cycleIncidencesDistinct :
          firstClauseIndex - boundary ≠
              secondClauseIndex - boundary ∨
            firstLiteralIndex ≠ secondLiteralIndex := by
        by_contra notDistinct
        simp only [not_or, not_not] at notDistinct
        have clauseIndexEq : firstClauseIndex = secondClauseIndex :=
          firstDecomposition.trans
            ((congrArg (fun index => boundary + index) notDistinct.1).trans
              secondDecomposition.symm)
        apply occurrencesDifferent
        simp only [Prod.mk.injEq]
        exact ⟨⟨clauseIndexEq, notDistinct.2⟩, translateZero.symm⟩
      exact cycleIncidencesDistinct

/-- The coordinate dispatcher recovers the standard flat incidence-indexed
relative certificate for the raw coordinated family. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther_of_copiedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (copiedSourceRelative :
      RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula) :=
  (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_coordinateRelativeAvoidEachOther_of_copiedSource
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty copiedSourceRelative).relative

/-- Relative separation survives the final pointwise unit subdivision and
loop erasure. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther_of_copiedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (copiedSourceRelative :
      RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula) := by
  apply
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther_of_copiedSource
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty copiedSourceRelative).normalizeOrthogonalIncidenceRoutes
  · intro incidence incidenceMember
    rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula)
        incidenceMember with
      ⟨clause, literal, clauseMember, literalMember,
        _incidenceEqual⟩
    have valid :=
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    intro routeEmpty
    have headNonempty := valid.1
    have routeEmpty' :
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
            formula incidence.1.clauseIndex incidence.1.literalIndex = [] := by
      simpa using routeEmpty
    simp [routeEmpty'] at headNonempty
  · intro incidence incidenceMember
    rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula)
        incidenceMember with
      ⟨clause, literal, clauseMember, literalMember,
        _incidenceEqual⟩
    exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

/-- Every stored route of the assembled normalized fixed-eight drawing is a
geometrically simple path. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_routesSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    ∀ route ∈
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
          formula).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  rw [retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing]
  apply PositionedPeriodicCNF.incidenceDrawing_routesSimple_of_pointwise
  intro clause clauseIndex clauseMember literal literalIndex literalMember
  exact
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_isSimple
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- The normalized assembled drawing inherits the incidence-level relative
certificate as separation of all distinct lifted route occurrences. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_relativeLiftedRoutesAvoidEachOther_of_copiedSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (copiedSourceRelative :
      RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).RelativeLiftedRoutesAvoidEachOther := by
  rw [retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing]
  exact
    PositionedPeriodicCNF.incidenceDrawing_relativeLiftedRoutesAvoidEachOther
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_pos
        formula)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_relativeAvoidEachOther_of_copiedSource
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty copiedSourceRelative)

/-- Subject only to copied-source/copy-source relative separation, the final
normalized fixed-eight drawing is ribbon-ready.  All mixed and cycle cases,
normalization transport, route simplicity, and unit-step obligations are
discharged internally. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_isRibbonReady_of_copiedSourceRelative
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (copiedSourceRelative :
      RetainedFinalCopiedSourceRoutesRelativeAvoidEachOther formula) :
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing
      formula).IsRibbonReady :=
  PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_relativeLiftedRoutesAvoidEachOther_of_copiedSource
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty copiedSourceRelative)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_routesSimple
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceDrawing_hasUnitSteps
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes

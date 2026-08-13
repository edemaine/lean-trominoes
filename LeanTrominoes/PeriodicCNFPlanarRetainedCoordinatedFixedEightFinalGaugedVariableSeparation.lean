/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalVariableOrbitSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedDrawing
import LeanTrominoes.PositionedPeriodicCNFVariableVertexPosition

/-!
# Variable separation in the final canonical gauge

Canonical quotient gauging turns equality of finite representatives into
equality modulo a whole raw period.  The raw orbit theorem therefore gives
ordinary injectivity on every variable that genuinely occurs in the final
formula, and hence pairwise distinct variable vertices.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance finalGaugedVariableSeparationDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Membership in the final clockwise presentation maps back to membership
in the raw composed formula because the final sort only permutes literals. -/
private theorem finalClockwiseVariableOccurrence_mem_composedRaw
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    atom ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase.variableOccurrences := by
  have occurrencePermutation :=
    PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact occurrencePermutation.mem_iff.mp
    (by
      simpa only [
        retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
        using atomMember)

/-- Every occurrence in the final gauged formula was already a genuine raw
composed occurrence. -/
theorem finalGaugedVariableOccurrence_mem_composedRaw
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    atom ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase.variableOccurrences := by
  apply finalClockwiseVariableOccurrence_mem_composedRaw
    source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    PeriodicCNF.variableOccurrences_variableGauge] using atomMember

/-- Canonically gauged positions identify genuine final variables. -/
theorem retainedOrderedFixedEightFinalGaugedVariablePosition_eq_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {first second :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (firstMember :
      first ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences)
    (secondMember :
      second ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences)
    (positionsEqual :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).position first =
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).position second) :
    first = second := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  have gaugedPositionsEqual :
      (rawPlacement.variableGauge rawPlacement.canonicalPositionGauge).position
          first =
        (rawPlacement.variableGauge rawPlacement.canonicalPositionGauge).position
          second := by
    simpa [rawPlacement,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge] using
        positionsEqual
  rcases
      PeriodicVariablePlacement.exists_translation_of_variableGauge_canonicalPositionGauge_position_eq
        rawPlacement gaugedPositionsEqual with
    ⟨relativeTranslate, rawPositionsEqual⟩
  exact
    retainedOrderedFixedEightComposedRawVariablePosition_eq_translated_imp_eq
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      (finalGaugedVariableOccurrence_mem_composedRaw
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstMember)
      (finalGaugedVariableOccurrence_mem_composedRaw
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondMember)
      relativeTranslate
      (by simpa [rawPlacement] using rawPositionsEqual)

/-- The variable-position prefix of the final incidence drawing has no
collisions. -/
theorem retainedOrderedFixedEightFinalGaugedVariablePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase.incidenceVariableVertices.map
      (PositionedPeriodicCNF.incidenceVariableVertexPosition
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source))).Nodup := by
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
  apply
    (List.nodup_dedup
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase.variableOccurrences).map_on
  intro first firstMember second secondMember positionsEqual
  apply retainedOrderedFixedEightFinalGaugedVariablePosition_eq_imp_eq
    source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
  · exact (List.mem_dedup.mp firstMember)
  · exact (List.mem_dedup.mp secondMember)
  · simpa [PositionedPeriodicCNF.incidenceVariableVertexPosition,
      Function.comp_def] using positionsEqual

end PeriodicOrthocrossing
end LeanTrominoes

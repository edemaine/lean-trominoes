/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDMComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDM
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationComputability

/-!
# Computability of the corrected polarity-normalized planar 3DM endpoint

The routed polarity-normalization layer uses route subdivision to position
its new vertices, but its erased formula is independent of those positions.
This module computes that erased formula directly, applies the final
clause-anchor normalization and finite 3DM encoder, and proves exact equality
with the proof-backed routed endpoint.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The fixed gauge that sends fresh complement literals to offset zero is
primitive recursive. -/
theorem freshGauge_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (freshGauge : PolarityNormalizedVariable Variable → Cell) := by
  have freshOffset : Primrec fun fresh : FreshOccurrence Variable =>
      fresh.2.offset :=
    PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd
  have fresh : Primrec fun occurrence : FreshOccurrence Variable =>
      Cell.sub (0, 0) occurrence.2.offset :=
    Computability.cell_sub_primrec.comp
      (Primrec.const ((0, 0) : Cell)) freshOffset
  exact (Primrec.sumCasesOn Primrec.id
    (Primrec.const ((0, 0) : Cell)).to₂
    (fresh.comp Primrec.snd).to₂).of_eq fun atom => by
      cases atom <;> rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision

namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

private abbrev FinalVariable (Variable : Type*) :=
  OneInThreeNoUnitVariable
    (PeriodicPlanarOneInThreeThreeRawVariable Variable)

local instance finalPolarityNormalizedComputabilityVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq (FinalVariable Variable) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem encodedProblem_congr
    {Variable : Type*} [DecidableEq Variable]
    {first second : PeriodicCNF Variable}
    (equal : first = second) :
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem first =
      PeriodicPlanarOneInThreeToThreeDM.encodedProblem second := by
  cases equal
  rfl

/-- Proof-free erased formula after the corrected routed polarity
normalization. -/
def
    retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF (PolarityNormalizedVariable (FinalVariable Variable)) :=
  (PeriodicOneInThreePolarityNormalization.formula
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
      source).erase.anchorNormalize)).variableGauge
        PeriodicOneInThreePolarityNormalizationRouteSubdivision.freshGauge

theorem
    retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed :
        PeriodicCNF Variable →
          PeriodicCNF
            (PolarityNormalizedVariable (FinalVariable Variable))) := by
  have normalizedSource : Primrec fun source : PeriodicCNF Variable =>
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        source).erase.anchorNormalize :=
    PeriodicCNF.anchorNormalize_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp
        retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_primrec)
  have logical : Primrec fun source : PeriodicCNF Variable =>
      PeriodicOneInThreePolarityNormalization.formula
        ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
          source).erase.anchorNormalize) :=
    PeriodicOneInThreePolarityNormalization.formula_primrec.comp
      normalizedSource
  have gauge : Primrec fun input : PeriodicCNF Variable ×
      PolarityNormalizedVariable (FinalVariable Variable) =>
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.freshGauge
        input.2 :=
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.freshGauge_primrec.comp
      Primrec.snd
  exact PeriodicCNF.variableGauge_primrec
    (fun source : PeriodicCNF Variable =>
      PeriodicOneInThreePolarityNormalization.formula
        ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
          source).erase.anchorNormalize))
    (fun _source =>
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.freshGauge)
    logical gauge

/-- For valid source data, the proof-free erased formula is exactly the
erasure of the routed polarity-normalized positioned formula. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed source =
      (PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).routes).erase := by
  rw [
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.erase_formula,
    retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty]
  simp only [
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinedSource,
    PositionedPeriodicCNF.erase_scale,
    PositionedPeriodicCNF.erase_anchorNormalize]

/-- The corrected polarity-normalized, padded planar 3DM endpoint with no
proof arguments in its runtime interface. -/
def
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.encodedProblem
    ((retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed
      source).anchorNormalize)

theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed :
        PeriodicCNF Variable → PeriodicThreeDM) := by
  exact PeriodicPlanarOneInThreeToThreeDM.encodedProblem_primrec.comp
    (PeriodicCNF.anchorNormalize_primrec.comp
      retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed_primrec)

theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable
      (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed :
        PeriodicCNF Variable → PeriodicThreeDM) :=
  retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_primrec.to_comp

/-- The proof-free corrected endpoint equals the routed, padded,
continuously planar 3DM problem on every valid source. -/
theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed
        source =
      retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty := by
  let routedFormula :=
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).routes
  let routedPlacement :=
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).routes
  have erasedEq :=
    retainedOrderedFixedEightPolarityNormalizedErasedFormulaComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have sourceEq := congrArg PeriodicCNF.anchorNormalize erasedEq
  have normalizedSourceEq :
      PeriodicPlanarOneInThreeToThreeDM.normalizedSource
          (routedFormula.scale 2) (routedPlacement.scale 2) =
        routedFormula.erase.anchorNormalize := by
    simpa only [PositionedPeriodicCNF.erase_scale] using
      PeriodicPlanarOneInThreeToThreeDM.normalizedSource_eq
        (routedFormula.scale 2) (routedPlacement.scale 2)
  have endpointSourceEq := sourceEq.trans normalizedSourceEq.symm
  unfold
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblemComputed
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
  exact encodedProblem_congr
    (Variable := PolarityNormalizedVariable (FinalVariable Variable))
    endpointSourceEq

end PeriodicOrthocrossing
end LeanTrominoes

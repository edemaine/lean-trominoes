/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDM
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalOrderingComputability
import LeanTrominoes.PeriodicCNFGaugeComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-!
# Computability of the final padded planar 3DM endpoint

The proof-carrying geometric construction chooses a final canonical variable
gauge, pads the complete drawing by a factor of two, and normalizes every
clause anchor before applying the finite Dyer--Frieze encoder.  This module
computes the same finite `PeriodicThreeDM` value without using any geometric
proof arguments and identifies it with the continuously planar endpoint.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

local instance finalGaugedRibbonThreeDMComputabilityVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem encodedProblem_congr
    {Variable : Type*} [DecidableEq Variable]
    {first second : PeriodicCNF Variable}
    (equal : first = second) :
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem first =
      PeriodicPlanarOneInThreeToThreeDM.encodedProblem second := by
  cases equal
  rfl

/-! ## Placement and gauge queries -/

/-- Positions in the source-scaled, fixed-eight placement are primitive
recursive. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable) =>
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        input.1).position input.2 := by
  let scaledPlacement := fun source : PeriodicCNF Variable =>
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).scale
      retainedAngularFanSourceClearanceFactor
  have scaledPosition : Primrec fun input : PeriodicCNF Variable ×
      WrappedPeriodicPlanarSATVariable Variable =>
      (scaledPlacement input.1).position input.2 := by
    exact Computability.cell_scale_primrec.comp
      (Primrec.const (retainedAngularFanSourceClearanceFactor : Int))
      retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec
  have splitPosition : Primrec fun input : PeriodicCNF Variable ×
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) =>
      (PeriodicEightOccurrenceSplitPositioned.placement
        (scaledPlacement input.1)).position input.2 :=
    PeriodicEightOccurrenceSplitPositioned.placement_position_primrec
      scaledPlacement scaledPosition
  exact (Computability.cell_scale_primrec.comp
    (Primrec.const (retainedTerminalFanRoutingRefinement : Int))
    splitPosition).of_eq fun _ => rfl

/-- Positions after the extra Figure 9 clearance scale are primitive
recursive. -/
theorem retainedFigureNineClearancePlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable) =>
      (retainedFigureNineClearancePlacement input.1).position input.2 := by
  exact (Computability.cell_scale_primrec.comp
    (Primrec.const (retainedFigureNineSourceClearanceFactor : Int))
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_primrec).of_eq
      fun _ => rfl

/-- The physical period of the twice-replaced raw placement is primitive
recursive. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period := by
  exact PlanarOneInThreeNoUnitsFigureNine.composedPlacement_period_primrec
    retainedFigureNineClearancePositionedFormula
    retainedFigureNineClearancePlacement
    retainedFigureNineClearancePlacement_period_primrec

/-- Every variable position in the twice-replaced raw placement is primitive
recursive. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable) =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        input.1).position input.2 := by
  exact PlanarOneInThreeNoUnitsFigureNine.composedPlacement_position_primrec
    retainedFigureNineClearancePositionedFormula
    retainedFigureNineClearancePlacement
    retainedFigureNineClearancePositionedFormula_primrec
    retainedFigureNineClearancePlacement_period_primrec
    retainedFigureNineClearancePlacement_position_primrec

/-- The final canonical quotient gauge is primitive recursive. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable) =>
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        input.1 input.2 := by
  exact PeriodicVariablePlacement.canonicalPositionGauge_primrec
    (fun source : PeriodicCNF Variable =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period)
    (fun source atom =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).position atom)
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_primrec
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_position_primrec

/-! ## Proof-free final formula and 3DM instance -/

/-- The final clockwise formula with its canonical variable gauge, computed
without geometric proof arguments. -/
def
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
    source).variableGauge
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        source)

theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed :
        PeriodicCNF Variable → _) := by
  exact PositionedPeriodicCNF.variableGauge_primrec
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed_primrec
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_primrec

/-- On a valid source, the proof-free gauged formula is exactly the geometric
pipeline's proof-backed final formula. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        source =
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty := by
  unfold
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty]

/-- The final padded, anchor-normalized planar 3DM instance, with all proof
arguments erased from its input interface. -/
def retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.encodedProblem
    (((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
      source).scale 2).erase.anchorNormalize)

theorem
    retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed :
        PeriodicCNF Variable → PeriodicThreeDM) := by
  have padded : Primrec fun source : PeriodicCNF Variable =>
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        source).scale 2 :=
    (PositionedPeriodicCNF.scale_primrec 2).comp
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_primrec
  have erased : Primrec fun source : PeriodicCNF Variable =>
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        source).scale 2).erase :=
    PositionedPeriodicCNF.erase_primrec.comp padded
  exact PeriodicPlanarOneInThreeToThreeDM.encodedProblem_primrec.comp
    (PeriodicCNF.anchorNormalize_primrec.comp erased)

theorem
    retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed :
        PeriodicCNF Variable → PeriodicThreeDM) :=
  retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed_primrec.to_comp

/-- On every valid hardness input, the proof-free finite instance is exactly
the endpoint equipped elsewhere with its continuously planar presentation. -/
theorem
    retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed
        source =
      retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty := by
  have normalizedSourceEq :
      (retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase =
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).scale 2).erase.anchorNormalize := by
    change PeriodicPlanarOneInThreeToThreeDM.normalizedSource
        ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).scale 2)
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).scale 2) = _
    exact PeriodicPlanarOneInThreeToThreeDM.normalizedSource_eq _ _
  have formulaEq :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have paddedFormulaEq := congrArg
    (fun formula : PositionedPeriodicCNF
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)) =>
      (formula.scale 2).erase.anchorNormalize)
    formulaEq
  have sourceEq := paddedFormulaEq.trans normalizedSourceEq.symm
  unfold
    retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblemComputed
    retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
  exact encodedProblem_congr
    (Variable :=
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
    (first :=
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed
        source).scale 2).erase.anchorNormalize)
    (second :=
      (retainedOrderedFixedEightFinalGaugedPaddedNormalizedSource
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).erase)
    sourceEq

end PeriodicOrthocrossing
end LeanTrominoes

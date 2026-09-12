/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFirstOccurrenceBits
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGadgetOriginCoordinateCompiler

/-! # Exactly one compiled gadget origin per actual horizontal clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicOneInThreePolarityNormalizationRouteSubdivision UnaryFieldBooleanFilter

/-- The actual clause gadget origins in clause presentation order. -/
def horizontalClauseGadgetOrigins (source : PeriodicCNF Nat) : List Cell :=
  (horizontalNormalizedRoutedFormulaComputed source).clauses.map fun clause =>
    Cell.add (Cell.scale 128 clause.position) (50, 60)

theorem horizontalClauseGadgetOrigins_eq_affine (source : PeriodicCNF Nat) :
    horizontalClauseGadgetOrigins source =
      (horizontalRoutedFormulaComputed source).clauses.map fun clause =>
        Cell.add (Cell.scale 256 (PositionedPeriodicCNF.canonicalClausePosition
          (horizontalRoutedPlacementComputed source) clause)) (50, 60) := by
  have scaleEq (point : Cell) : Cell.scale 128 (Cell.scale 2 point) = Cell.scale 256 point := by
    rcases point with ⟨x, y⟩
    apply Prod.ext <;> dsimp only [Cell.scale] <;> omega
  unfold horizontalClauseGadgetOrigins
  rw [horizontalNormalizedRoutedFormulaComputed_eq_normalizedSource]
  simp only [PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource,
    PositionedPeriodicCNF.anchorNormalize, PositionedPeriodicCNF.scale_clauses, List.map_map,
    Function.comp_def, PositionedPeriodicCNF.canonicalClausePosition_scale, Nat.cast_ofNat, scaleEq]

@[simp] theorem horizontalClauseGadgetOrigins_length (source : PeriodicCNF Nat) :
    (horizontalClauseGadgetOrigins source).length = (horizontalRoutedFormulaComputed source).clauses.length := by
  rw [horizontalClauseGadgetOrigins_eq_affine, List.length_map]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- First-occurrence filtering removes repeated clause-origin coordinates. -/
def directSourceFinalClauseGadgetOriginCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  selectedValues (directSourceFinalClauseFirstBits decider symbols)
    (directSourceFinalGadgetOriginCoordinates decider false horizontal keepPositive symbols)

noncomputable def directSourceFinalClauseGadgetOriginCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseGadgetOriginCoordinates decider horizontal keepPositive) :=
  selectedValuesNativeListComputableInPolyTime
    (directSourceFinalClauseFirstBits decider)
    (directSourceFinalGadgetOriginCoordinates decider false horizontal keepPositive)
    (directSourceFinalClauseFirstBitsComputableInPolyTime decider)
    (directSourceFinalGadgetOriginCoordinatesComputableInPolyTime decider false horizontal keepPositive)

/-- The filtered column contains exactly one actual origin per clause, in
its original order, with no distinctness assumption on coordinates. -/
theorem directSourceFinalClauseGadgetOriginCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalClauseGadgetOriginCoordinates decider horizontal keepPositive symbols =
      (horizontalClauseGadgetOrigins (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
        (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)) := by
  unfold directSourceFinalClauseGadgetOriginCoordinates
  rw [directSourceFinalClauseFirstBits_eq_horizontal, directSourceFinalGadgetOriginCoordinates_eq_affine,
    horizontalClauseGadgetOrigins_eq_affine, List.map_map]
  simp only [directSourceFinalRoutedVertexPoints, horizontalGadgetOriginOffset, Bool.false_eq_true, ↓reduceIte,
    presentedIncidenceClausePositions, List.map_flatMap, List.map_replicate, Function.comp_def]
  exact selectedValues_firstBlocks _ _ _
    (horizontalRoutedClause_length_pos (PolySpaceCompiler.formulaOfSymbols decider symbols))

@[simp] theorem directSourceFinalClauseGadgetOriginCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalClauseGadgetOriginCoordinates decider horizontal keepPositive symbols).length =
      (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.length := by
  rw [directSourceFinalClauseGadgetOriginCoordinates_eq_horizontal, List.length_map, horizontalClauseGadgetOrigins_length]

end LeanTrominoes.PeriodicCNFStripReduction
end

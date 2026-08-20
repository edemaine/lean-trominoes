/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPreparedHeaderSemantics
import LeanTrominoes.PeriodicCNFStripDirectGridUnitData
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedAssignmentData
import LeanTrominoes.PeriodicCNFStripHorizontalPeriodSize

/-! # Exact unary scale of the direct 3DM drawing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Product of the fixed geometric refinements between the source
orthocrossing grid and the assembled 3DM drawing. -/
def directDrawingGridFactor : Nat :=
  PeriodicPlanarOneInThreeToThreeDM.standardThreeStrandLayout.factor *
    2 *
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinementFactor *
        horizontalPlacementPeriodFactor

/-- Expand each source-grid marker into the fixed number of assembled-drawing
grid markers. -/
def drawingGridUnits (units : List Unit) : List Unit :=
  units.flatMap fun _ => List.replicate directDrawingGridFactor ()

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directDrawingGridUnitsDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Unary assembled-drawing grid scale generated from raw source symbols. -/
def directDrawingGridUnitsOfSymbols (symbols : List encoding.Γ) : List Unit :=
  drawingGridUnits (directGridUnitsOfSymbols decider symbols)

theorem directSparseComputedNormalizationInput_drawing_gridSize_eq
    (symbols : List encoding.Γ) :
    (directSparseComputedNormalizationInputOfSymbols decider symbols).drawing.gridSize =
      directDrawingGridFactor *
        sourceOrthocrossingGridSize
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  rw [directSparseComputedNormalizationInputOfSymbols_eq]
  simp only [directSparseNormalizationInputOfSymbols,
    normalizationInput_drawing]
  rw [presentation_drawing_gridSize_eq, horizontalPlacement_period_eq]
  unfold directDrawingGridFactor
  ring

/-- The emitted unary word has exactly the assembled drawing's grid size. -/
@[simp] theorem directDrawingGridUnitsOfSymbols_eq_replicate
    (symbols : List encoding.Γ) :
    directDrawingGridUnitsOfSymbols decider symbols =
      List.replicate
        (directSparseComputedNormalizationInputOfSymbols
          decider symbols).drawing.gridSize () := by
  unfold directDrawingGridUnitsOfSymbols drawingGridUnits
  rw [directGridUnitsOfSymbols_eq_replicate,
    GadgetPreparedHeaderEmitter.flatMap_replicate_const,
    GadgetPreparedHeaderEmitter.replicate_flatten_replicate,
    directSparseComputedNormalizationInput_drawing_gridSize_eq]
  exact congrArg (fun count => List.replicate count ())
    (Nat.mul_comm _ _)

@[simp] theorem directDrawingGridUnitsOfSymbols_length
    (symbols : List encoding.Γ) :
    (directDrawingGridUnitsOfSymbols decider symbols).length =
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).drawing.gridSize := by
  rw [directDrawingGridUnitsOfSymbols_eq_replicate]
  simp

end PeriodicCNFStripReduction
end LeanTrominoes

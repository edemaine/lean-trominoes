/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.PeriodicCNFFormulaShapeSourceAtomCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeVariableCount
import LeanTrominoes.PeriodicOrthocrossingRetainedSourceAtomPosition

/-! # Direct-source original-atom coordinate compilers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directOriginalAtomCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private theorem sourceShape_variableCount (symbols : List encoding.Γ) :
    FormulaShape.variableCount (directSourceFormulaShape decider symbols) =
      (directSourceFormula decider symbols).variableOccurrences.dedup.length := by
  exact directSourceFormulaShape_variableCount_eq decider symbols

/-- Original source-variable indices in deduplicated occurrence order. -/
def directSourceOriginalAtomIndices (symbols : List encoding.Γ) : List Nat :=
  FormulaShapeSourceAtomCoordinates.indices (directSourceFormulaShape decider symbols)

noncomputable def directSourceOriginalAtomIndicesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat) encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceOriginalAtomIndices decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols => FormulaShapeSourceAtomCoordinates.indices
      (directSourceFormulaShape decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFormulaShapeComputableInPolyTime decider)
    FormulaShapeSourceAtomCoordinates.indicesComputableInPolyTime

theorem directSourceOriginalAtomIndices_eq_range (symbols : List encoding.Γ) :
    directSourceOriginalAtomIndices decider symbols =
      List.range (directSourceFormula decider symbols).variableOccurrences.dedup.length := by
  unfold directSourceOriginalAtomIndices FormulaShapeSourceAtomCoordinates.indices
  rw [sourceShape_variableCount]

/-- Four signed fields of the actual canonically gauged original-atom positions. -/
def directSourceOriginalAtomCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  FormulaShapeSourceAtomCoordinates.values horizontal keepPositive
    (directSourceFormulaShape decider symbols)

noncomputable def directSourceOriginalAtomCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat) encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceOriginalAtomCoordinates decider horizontal keepPositive) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols => FormulaShapeSourceAtomCoordinates.values horizontal keepPositive
      (directSourceFormulaShape decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFormulaShapeComputableInPolyTime decider)
    (FormulaShapeSourceAtomCoordinates.valuesComputableInPolyTime horizontal keepPositive)

/-- No source-coordinate premise remains: the formula-shape machine emits the
actual gauged placement coordinate of every deduplicated original atom. -/
theorem directSourceOriginalAtomCoordinates_eq_positions
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceOriginalAtomCoordinates decider horizontal keepPositive symbols =
      (directSourceFormula decider symbols).variableOccurrences.dedup.map fun atom =>
        let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          (directSourceFormula decider symbols)).position ⟨.atom atom⟩
        let coordinate := if horizontal then position.1 else position.2
        if keepPositive then coordinate.toNat else (-coordinate).toNat := by
  unfold directSourceOriginalAtomCoordinates
  exact retainedSourceAtomCoordinateFields_eq_positions horizontal keepPositive
    (directSourceFormula decider symbols) (directSourceFormulaShape decider symbols)
    (sourceShape_variableCount decider symbols)

/-- Every signed column has one entry for each distinct original variable. -/
theorem directSourceOriginalAtomCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceOriginalAtomCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFormula decider symbols).variableOccurrences.dedup.length := by
  rw [directSourceOriginalAtomCoordinates_eq_positions]
  exact List.length_map _

end LeanTrominoes.PeriodicCNFStripReduction

end

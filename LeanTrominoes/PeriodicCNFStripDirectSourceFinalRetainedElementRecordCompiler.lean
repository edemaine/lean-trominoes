/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRetainedElementCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTableAppenderData
import LeanTrominoes.PeriodicCNFStripDirectDrawingGridUnitEmitter
import LeanTrominoes.GadgetSparseAffineVertexRecordColumnCompiler
import LeanTrominoes.UnaryFieldConstantBitCompiler

/-! # Unconditional affine records for all retained colored elements -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing Gadget PeriodicOrthocrossing

local instance retainedElementRecordCellTypeInhabited : Inhabited OrthogonalCellType := ⟨.monochromaticVertex .red⟩

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private noncomputable def retainedCoordinateCompiler (color : WireColor) (horizontal : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalRetainedElementPositions
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) color).map
          (fun point => (DelimitedDirectionDisplacement.component horizontal point).toNat)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalRetainedElementCoordinatesComputableInPolyTime decider color horizontal true)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields (by
      rw [directSourceFinalRetainedElementCoordinates_eq_horizontal]
      cases horizontal <;> rfl))

private noncomputable def retainedCellTypeCompiler (color : WireColor) :
    TM2ComputableInPolyTime id id
      (fun symbols => (horizontalRetainedElementPositions
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) color).map
          (fun _ => OrthogonalCellType.monochromaticVertex color)) := by
  let bits := TM2CompositionMachine.computableInPolyTime
    (retainedCoordinateCompiler decider color true)
    (UnaryFieldConstantBits.computableInPolyTime true)
  let cells := TM2CompositionMachine.computableInPolyTime bits
    (FiniteBlockTransducer.computableInPolyTime
      (fun _ : Bool => [OrthogonalCellType.monochromaticVertex color]))
  apply Turing.TM2ComputableInPolyTime.of_eq cells
  intro symbols
  simp only [UnaryFieldConstantBits.values, List.flatMap_map, ← List.map_eq_flatMap, List.map_map]

/-- Complete compact affine records for a color's actual retained vertices,
including the exact grid reflection and monochromatic cell-type field. -/
noncomputable def directSourceFinalRetainedElementRecordsComputableInPolyTime (color : WireColor) :
    TM2ComputableInPolyTime id id
      (directSparseComputedAffineTableElementRequestsOfSymbols decider color) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let compiler := GadgetSparseAffineVertexTokens.RecordColumns.computableInPolyTimeOf
      (fun symbols => horizontalRetainedElementPositions
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) color)
      (directDrawingGridUnitsOfSymbols decider)
      (fun _ point => (DelimitedDirectionDisplacement.component true point).toNat)
      (fun _ point => (DelimitedDirectionDisplacement.component false point).toNat)
      (fun _ _ => OrthogonalCellType.monochromaticVertex color)
      (retainedCoordinateCompiler decider color true)
      (retainedCoordinateCompiler decider color false)
      (retainedCellTypeCompiler decider color)
      (directDrawingGridUnitsOfSymbolsComputableInPolyTime decider)
    apply Turing.TM2ComputableInPolyTime.of_eq compiler
    intro symbols
    rw [directDrawingGridUnitsOfSymbols_length]
    unfold directSparseComputedAffineTableElementRequestsOfSymbols
      directSparseComputedAffineTableClauseElementRequests horizontalRetainedElementPositions
    rw [List.flatMap_assoc]
    rfl
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction
end

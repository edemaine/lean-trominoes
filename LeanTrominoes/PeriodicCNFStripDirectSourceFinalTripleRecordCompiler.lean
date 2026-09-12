/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTripleCellTypeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexIndexedAppenderData
import LeanTrominoes.PeriodicCNFStripDirectDrawingGridUnitEmitter
import LeanTrominoes.GadgetSparseAffineVertexRecordColumnCompiler

/-! # Unconditional affine records for the complete actual triple prefix -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing Gadget PeriodicOrthocrossing

private theorem positivePointValue (horizontal : Bool) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal true) =
      (fun point => (DelimitedDirectionDisplacement.component horizontal point).toNat) := by
  funext point
  cases horizontal <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private noncomputable def tripleCoordinateCompiler (horizontal : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalThreeDMTriplePositionsComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).zipIdx.map
          (fun tagged => (DelimitedDirectionDisplacement.component horizontal tagged.1).toNat)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalTripleCoordinatesComputableInPolyTime decider horizontal true)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields (by
      rw [directSourceFinalTripleCoordinates_eq_horizontal, positivePointValue]
      simpa only [List.map_map, Function.comp_def] using
        (congrArg (List.map (fun point => (DelimitedDirectionDisplacement.component horizontal point).toNat))
          (List.zipIdx_map_fst 0 (horizontalThreeDMTriplePositionsComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)))).symm))

private noncomputable def tripleCellTypeCompiler :
    @TM2ComputableInPolyTime (List encoding.Γ) (List OrthogonalCellType) encoding.Γ OrthogonalCellType id id
      (fun symbols => (horizontalThreeDMTriplePositionsComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).zipIdx.map
          (fun tagged => PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
            (horizontalNormalizationInputComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
              (.triple tagged.2))) := by
  have equal : directSourceFinalTripleCellTypes decider =
      (fun symbols => (horizontalThreeDMTriplePositionsComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).zipIdx.map
          (fun tagged => PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
            (horizontalNormalizationInputComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
              (.triple tagged.2))) :=
    funext (directSourceFinalTripleCellTypes_eq_indexedPositions decider)
  rw [← equal]
  exact directSourceFinalTripleCellTypesComputableInPolyTime decider

/-- Serialize all variable and clause triples in the original stable index order. -/
noncomputable def directSourceFinalTripleRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSparseComputedAffineIndexedTripleRequestsOfSymbols decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let compiler := GadgetSparseAffineVertexTokens.RecordColumns.computableInPolyTimeOf
      (fun symbols => (horizontalThreeDMTriplePositionsComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).zipIdx)
      (directDrawingGridUnitsOfSymbols decider)
      (fun _ tagged => (DelimitedDirectionDisplacement.component true tagged.1).toNat)
      (fun _ tagged => (DelimitedDirectionDisplacement.component false tagged.1).toNat)
      (fun symbols tagged => PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
          (.triple tagged.2))
      (tripleCoordinateCompiler decider true)
      (tripleCoordinateCompiler decider false)
      (tripleCellTypeCompiler decider)
      (directDrawingGridUnitsOfSymbolsComputableInPolyTime decider)
    apply Turing.TM2ComputableInPolyTime.of_eq compiler
    intro symbols
    rw [directDrawingGridUnitsOfSymbols_length]
    unfold directSparseComputedAffineIndexedTripleRequestsOfSymbols
      directSparseComputedAffineIndexedTripleRequests
    apply List.flatMap_congr
    intro tagged _
    rfl
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction
end

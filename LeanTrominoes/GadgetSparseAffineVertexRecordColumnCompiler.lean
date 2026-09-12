/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetRecordColumnCompiler
import LeanTrominoes.GadgetSparseAffineVertexTokens
import LeanTrominoes.UnaryFieldUnitLengthBroadcastCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.UnaryAlignedDifferenceCompiler

/-! # Affine vertex records from compiled coordinates, grid units, and cell types -/

noncomputable section
namespace LeanTrominoes.GadgetSparseAffineVertexTokens.RecordColumns
open Computability Turing Gadget FiniteAlphabetRecordColumns

/-- Grid reflection preserves the coordinate column's order. -/
def reflected (vertical : List Nat) (units : List Unit) : List Nat :=
  UnaryAlignedDifference.values true
    (UnaryFieldConstantScale.values 2 (UnaryFieldUnitLengthBroadcast.values vertical units))
    (UnaryFieldConstantOffsets.values 1 vertical)

theorem reflected_eq_map (vertical : List Nat) (units : List Unit) :
    reflected vertical units = vertical.map (fun value => 2 * units.length - value - 1) := by
  unfold reflected
  rw [UnaryFieldUnitLengthBroadcast.values_eq_map, UnaryAlignedDifference.values_eq_zipWith]
  unfold UnaryFieldConstantScale.values UnaryFieldConstantOffsets.values
  simp only [List.map_map, Function.comp_def]
  induction vertical with
  | nil => rfl
  | cons value vertical induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, ↓reduceIte]
      congr 1
      omega

noncomputable def reflectedComputableInPolyTime
    {SourceSymbol : Type} [Fintype SourceSymbol]
    (vertical : List SourceSymbol → List Nat) (units : List SourceSymbol → List Unit)
    (verticalCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields vertical)
    (unitCompiler : TM2ComputableInPolyTime id id units) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => reflected (vertical source) (units source)) := by
  unfold reflected
  exact UnaryAlignedDifference.nativeListComputableInPolyTime true _ _
    (fun source => by simp only [UnaryFieldConstantScale.values, UnaryFieldConstantOffsets.values,
      List.length_map, UnaryFieldUnitLengthBroadcast.values_length])
    (TM2CompositionMachine.computableInPolyTime
      (UnaryFieldUnitLengthBroadcast.nativeListComputableInPolyTime vertical units verticalCompiler unitCompiler)
      (UnaryFieldConstantScale.computableInPolyTime 2))
    (TM2CompositionMachine.computableInPolyTime verticalCompiler
      (UnaryFieldConstantOffsets.computableInPolyTime 1))

/-- All fields are independently compiled but assembled in their common row order.
The unit word supplies the actual grid scale used for vertical reflection. -/
noncomputable def computableInPolyTimeOf
    {SourceSymbol Row : Type} [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (rows : List SourceSymbol → List Row) (units : List SourceSymbol → List Unit)
    (horizontal vertical : List SourceSymbol → Row → Nat)
    (cellType : List SourceSymbol → Row → OrthogonalCellType)
    (horizontalCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => (rows source).map (horizontal source)))
    (verticalCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => (rows source).map (vertical source)))
    (cellTypeCompiler : TM2ComputableInPolyTime id id
      (fun source => (rows source).map (cellType source)))
    (unitCompiler : TM2ComputableInPolyTime id id units) :
    TM2ComputableInPolyTime id id
      (fun source => (rows source).flatMap
        (fun row => record (horizontal source row) (2 * (units source).length - vertical source row - 1) (cellType source row))) := by
  let horizontalBlocks := TM2CompositionMachine.computableInPolyTime horizontalCompiler
    (unaryBlocksComputableInPolyTime Token.scaledCoordinateUnit [.horizontalOffset, .fieldEnd])
  let reflectedCompiler := reflectedComputableInPolyTime _ units verticalCompiler unitCompiler
  let verticalValues : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => (rows source).map (fun row => 2 * (units source).length - vertical source row - 1)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq reflectedCompiler (fun source => by
      rw [reflected_eq_map, List.map_map]
      rfl)
  let verticalBlocks := TM2CompositionMachine.computableInPolyTime verticalValues
    (unaryBlocksComputableInPolyTime Token.scaledCoordinateUnit [.verticalOffset])
  let cellBlocks := TM2CompositionMachine.computableInPolyTime cellTypeCompiler
    (FiniteBlockTransducer.computableInPolyTime (fun value : OrthogonalCellType =>
      FiniteAlphabetDelimitedBlockJoin.block [Token.cellType value]))
  let coordinates := joinedFieldsComputableInPolyTime id rows _ _
    (by simpa only [List.map_map, Function.comp_def] using horizontalBlocks)
    (by simpa only [List.map_map, Function.comp_def] using verticalBlocks)
  let complete := joinedFieldsComputableInPolyTime id rows _ _ coordinates
    (by simpa only [FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map] using cellBlocks)
  let flattened := flattenBlocksComputableInPolyTime id _ complete
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq flattened (fun source => by
    rw [← List.flatMap_def]
    apply List.flatMap_congr
    intro row _
    simp [record, List.append_assoc])

end LeanTrominoes.GadgetSparseAffineVertexTokens.RecordColumns
end

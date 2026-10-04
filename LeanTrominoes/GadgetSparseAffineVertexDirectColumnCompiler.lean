/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetSparseAffineVertexRecordColumnCompiler

/-! # Compact affine records from horizontal and reflected-vertical columns -/
noncomputable section
namespace LeanTrominoes.GadgetSparseAffineVertexTokens.DirectColumns
open _root_.Computability Turing Gadget FiniteAlphabetRecordColumns

def computableInPolyTimeOf {Source Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
    (encodeSource : Source → List Symbol) (rows : Source → List Row)
    (horizontal verticalComplement : Source → Row → Nat)
    (cellType : Source → Row → OrthogonalCellType)
    (xCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => (rows source).map (horizontal source)))
    (yCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => (rows source).map (verticalComplement source)))
    (cellCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => (rows source).map (cellType source))) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => (rows source).flatMap (fun row =>
        record (horizontal source row) (verticalComplement source row) (cellType source row))) := by
  let xs := TM2CompositionMachine.computableInPolyTime xCompiler
    (unaryBlocksComputableInPolyTime Token.scaledCoordinateUnit [.horizontalOffset,.fieldEnd])
  let ys := TM2CompositionMachine.computableInPolyTime yCompiler
    (unaryBlocksComputableInPolyTime Token.scaledCoordinateUnit [.verticalOffset])
  let cells := TM2CompositionMachine.computableInPolyTime cellCompiler
    (FiniteBlockTransducer.computableInPolyTime (fun cell : OrthogonalCellType =>
      FiniteAlphabetDelimitedBlockJoin.block [Token.cellType cell]))
  let coordinates := joinedFieldsComputableInPolyTime encodeSource rows _ _
    (by simpa only [List.map_map,Function.comp_def] using xs)
    (by simpa only [List.map_map,Function.comp_def] using ys)
  let complete := joinedFieldsComputableInPolyTime encodeSource rows _ _ coordinates
    (by simpa only [FiniteAlphabetDelimitedBlockJoin.blocks,List.flatMap_map] using cells)
  let flattened := flattenBlocksComputableInPolyTime encodeSource _ complete
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq flattened (fun source => by
    rw [←List.flatMap_def]
    apply List.flatMap_congr
    intro row _
    simp [record,List.append_assoc])
end LeanTrominoes.GadgetSparseAffineVertexTokens.DirectColumns

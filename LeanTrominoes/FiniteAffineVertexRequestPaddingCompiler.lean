/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteSparsePaddingColumns
import LeanTrominoes.GadgetSparseAffineVertexColumnProjection
import LeanTrominoes.GadgetSparseAffineVertexDirectColumnCompiler
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Pad an already compiled compact affine vertex stream -/
noncomputable section
namespace LeanTrominoes.FiniteAffineVertexRequestPaddingCompiler
open _root_.Computability Turing Gadget GadgetSparseAffineVertexTokens
open UnaryFieldEncoderMachine (unaryFields)
local instance : Inhabited OrthogonalCellType := ⟨.blank⟩

/-- Reuse the complete original vertex emitter. Finite-state column
projections, unary addition, and record assembly perform the padding. -/
def computableInPolyTime {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
    (rows : List Symbol → List Row) (units : List Symbol → List Unit)
    (horizontal verticalComplement : List Symbol → Row → Nat)
    (cellType : List Symbol → Row → OrthogonalCellType)
    (emitter : TM2ComputableInPolyTime id id
      (fun source => (rows source).flatMap (fun row =>
        record (horizontal source row) (verticalComplement source row) (cellType source row))))
    (unitCompiler : TM2ComputableInPolyTime id id units) :
    TM2ComputableInPolyTime id id
      (fun source => (rows source).flatMap (fun row =>
        record (horizontal source row+(units source).length)
          (verticalComplement source row+3*(units source).length+2) (cellType source row))) := by
  let x := TM2CompositionMachine.computableInPolyTime emitter (ColumnProjection.computableInPolyTime false)
  let y := TM2CompositionMachine.computableInPolyTime emitter (ColumnProjection.computableInPolyTime true)
  let xCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (rows source).map (horizontal source)) :=
    TM2PolyTimeOutputEncodingTransport.of_identity_output_eq x
      (fun source => by simpa only [Bool.false_eq_true,↓reduceIte] using
        ColumnProjection.output_records (rows source) (horizontal source) (verticalComplement source) (cellType source) false)
  let yCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (rows source).map (verticalComplement source)) :=
    TM2PolyTimeOutputEncodingTransport.of_identity_output_eq y
      (fun source => by simpa only [↓reduceIte] using
        ColumnProjection.output_records (rows source) (horizontal source) (verticalComplement source) (cellType source) true)
  let cells := TM2CompositionMachine.computableInPolyTime emitter
    (FiniteBlockTransducer.computableInPolyTime ColumnProjection.cellBlock)
  let cellCompiler : TM2ComputableInPolyTime id id
      (fun source => (rows source).map (cellType source)) :=
    cells.of_eq (fun source => ColumnProjection.cellBlock_records _ _ _ _)
  let paddedX := FiniteSparsePaddingColumns.coordinatesComputableInPolyTime
    (fun source => (rows source).map (horizontal source)) units xCompiler unitCompiler
  let paddedY := FiniteSparsePaddingColumns.complementsComputableInPolyTime
    (fun source => (rows source).map (verticalComplement source)) units yCompiler unitCompiler
  refine DirectColumns.computableInPolyTimeOf id rows
    (fun source row => horizontal source row+(units source).length)
    (fun source row => verticalComplement source row+3*(units source).length+2)
    cellType ?_ ?_ cellCompiler
  · exact paddedX.of_eq (fun source => by rw [FiniteSparsePaddingColumns.coordinates_eq_map,List.map_map];rfl)
  · exact paddedY.of_eq (fun source => by rw [FiniteSparsePaddingColumns.complements_eq_map,List.map_map];rfl)
end LeanTrominoes.FiniteAffineVertexRequestPaddingCompiler

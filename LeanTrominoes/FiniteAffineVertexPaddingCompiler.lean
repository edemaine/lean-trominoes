/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteSparsePaddingColumns
import LeanTrominoes.GadgetSparseAffineVertexRecordColumnCompiler
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Polynomial-time compact vertex records for the padded finite input -/
noncomputable section
namespace LeanTrominoes.GadgetSparseAffineVertexTokens.RecordColumns
open _root_.Computability Turing Gadget
open UnaryFieldEncoderMachine (unaryFields)

variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
variable (rows : List Symbol → List Row) (units : List Symbol → List Unit)
variable (horizontal vertical : List Symbol → Row → Nat)
variable (cellType : List Symbol → Row → OrthogonalCellType)
variable (horizontalCompiler : TM2ComputableInPolyTime id unaryFields
    (fun source => (rows source).map (horizontal source)))
variable (verticalCompiler : TM2ComputableInPolyTime id unaryFields
    (fun source => (rows source).map (vertical source)))
variable (cellTypeCompiler : TM2ComputableInPolyTime id id
    (fun source => (rows source).map (cellType source)))
variable (unitCompiler : TM2ComputableInPolyTime id id units)

/-- Each original coordinate gains one grid-size offset. The enlarged grid
is used for reflection, while row order and the finite cell type are retained. -/
def finitePadComputableInPolyTime : TM2ComputableInPolyTime id id
    (fun source => (rows source).flatMap (fun row =>
      record (horizontal source row+(units source).length)
        (2*(3*(units source).length+1)-(vertical source row+(units source).length)-1)
        (cellType source row))) := by
  let x := FiniteSparsePaddingColumns.coordinatesComputableInPolyTime
    (fun source => (rows source).map (horizontal source)) units horizontalCompiler unitCompiler
  let y := FiniteSparsePaddingColumns.coordinatesComputableInPolyTime
    (fun source => (rows source).map (vertical source)) units verticalCompiler unitCompiler
  let xCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (rows source).map (fun row => horizontal source row+(units source).length)) :=
    x.of_eq (fun source => by
      rw [FiniteSparsePaddingColumns.coordinates_eq_map,List.map_map];rfl)
  let yCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (rows source).map (fun row => vertical source row+(units source).length)) :=
    y.of_eq (fun source => by
      rw [FiniteSparsePaddingColumns.coordinates_eq_map,List.map_map];rfl)
  let compiler := computableInPolyTimeOf rows
    (fun source => FiniteSparsePaddingColumns.gridUnits (units source))
    (fun source row => horizontal source row+(units source).length)
    (fun source row => vertical source row+(units source).length) cellType
    xCompiler yCompiler cellTypeCompiler
    (FiniteSparsePaddingColumns.gridUnitsComputableInPolyTime units unitCompiler)
  exact compiler.of_eq (fun source => by rw [FiniteSparsePaddingColumns.gridUnits_length])
end LeanTrominoes.GadgetSparseAffineVertexTokens.RecordColumns

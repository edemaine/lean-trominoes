/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseAffineVertexTokens
import LeanTrominoes.Complexity.FiniteStateTransducerTime
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Actual finite-state projections of compact affine vertex records -/
noncomputable section
namespace LeanTrominoes.GadgetSparseAffineVertexTokens.ColumnProjection
open _root_.Computability Turing Gadget FiniteStateTransducer
open UnaryFieldEncoderMachine (unaryField unaryFields)

def transition (selectVertical : Bool) : Bool → Token → Bool × List UnaryFieldEncoderMachine.Symbol
  | phase,.scaledCoordinateUnit => (phase,if phase=selectVertical then [.unit] else [])
  | _,.horizontalOffset => (false,[])
  | _,.fieldEnd => (true,if selectVertical then [] else [.delimiter])
  | phase,.verticalOffset => (phase,[])
  | _,.cellType _ => (false,if selectVertical then [.delimiter] else [])

def output (selectVertical : Bool) : List Token → List UnaryFieldEncoderMachine.Symbol :=
  FiniteStateTransducer.output false (transition selectVertical) (fun _ => [])

private theorem scan_units (selectVertical phase : Bool) (count : Nat) (tail : List Token) :
    scan (transition selectVertical) phase (List.replicate count .scaledCoordinateUnit++tail)=
      ((scan (transition selectVertical) phase tail).1,
        (if phase=selectVertical then List.replicate count .unit else [])++
        (scan (transition selectVertical) phase tail).2) := by
  induction count with
  | zero => cases phase <;> cases selectVertical <;> simp
  | succ count ih =>
      rw [List.replicate_succ,List.cons_append]
      simp only [scan,transition]
      rw [ih]
      cases phase <;> cases selectVertical <;> simp [List.replicate_succ]

private theorem scan_record (selectVertical : Bool) (x y : Nat) (cell : OrthogonalCellType) (tail : List Token) :
    scan (transition selectVertical) false (record x y cell++tail)=
      ((scan (transition selectVertical) false tail).1,
        unaryField (if selectVertical then y else x)++(scan (transition selectVertical) false tail).2) := by
  simp only [record,List.append_assoc,List.cons_append,List.nil_append]
  rw [scan_units]
  simp only [scan,transition,List.nil_append]
  rw [scan_units]
  cases selectVertical <;> simp [scan,transition,unaryField,List.append_assoc]

/-- Every coordinate column is extracted in the original row order. -/
theorem output_records {Row : Type} (rows : List Row) (x y : Row → Nat) (cell : Row → OrthogonalCellType)
    (selectVertical : Bool) :
    output selectVertical (rows.flatMap (fun row => record (x row) (y row) (cell row)))=
      unaryFields (rows.map (fun row => if selectVertical then y row else x row)) := by
  have eq : scan (transition selectVertical) false
      (rows.flatMap (fun row => record (x row) (y row) (cell row)))=
      (false,unaryFields (rows.map (fun row => if selectVertical then y row else x row))) := by
    induction rows with
    | nil => rfl
    | cons row rows ih =>
        rw [List.flatMap_cons,scan_record,ih]
        simp only [List.map_cons,UnaryFieldEncoderMachine.unaryFields_cons]
  simp only [output,FiniteStateTransducer.output,eq,List.append_nil]

def cellBlock : Token → List OrthogonalCellType
  | .cellType cell => [cell]
  | _ => []

private theorem cellBlock_units (count : Nat) :
    (List.replicate count Token.scaledCoordinateUnit).flatMap cellBlock=[] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ,cellBlock,ih]

private theorem cellBlock_record (x y : Nat) (cell : OrthogonalCellType) :
    (record x y cell).flatMap cellBlock=[cell] := by
  simp [record,cellBlock,cellBlock_units]

theorem cellBlock_records {Row : Type} (rows : List Row) (x y : Row → Nat) (cell : Row → OrthogonalCellType) :
    (rows.flatMap (fun row => record (x row) (y row) (cell row))).flatMap cellBlock=rows.map cell := by
  simp only [List.flatMap_assoc,cellBlock_record,←List.map_eq_flatMap]

def computableInPolyTime (selectVertical : Bool) : TM2ComputableInPolyTime id id (output selectVertical) :=
  FiniteStateTransducer.computableInPolyTime false (transition selectVertical) (fun _ => [])
end LeanTrominoes.GadgetSparseAffineVertexTokens.ColumnProjection

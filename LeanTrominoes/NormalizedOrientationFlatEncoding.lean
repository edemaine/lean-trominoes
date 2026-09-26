/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetReductionComputability
import LeanTrominoes.PeriodicCNFFlatEncoding

/-! # A native flat binary encoding of normalized orientation drawings

The two positive periods precede the complete row-major cell table. Colors,
bends, and vertex types are retained, including on malformed input drawings.
-/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.FlatEncoding
open PeriodicOrthogonalDrawing

def cellCode (k : OrthogonalCellType) : Nat :=
  if k = .blank then 0 else Encodable.encode k + 1

def decodeCell : Nat → Option OrthogonalCellType
  | 0 => some .blank
  | n+1 => Encodable.decode n

@[simp] theorem cellCode_blank : cellCode .blank = 0 := by simp [cellCode]

@[simp] theorem decodeCell_cellCode (k : OrthogonalCellType) :
    decodeCell (cellCode k) = some k := by
  by_cases h : k = .blank
  · subst k; rfl
  · simp [cellCode,h,decodeCell,Encodable.encodek]

theorem cellCode_injective : Function.Injective cellCode := by
  intro a b h
  have := congrArg decodeCell h
  simpa using this

def fields (d : PeriodicOrthogonalDrawing) : List Nat :=
  d.horizontalPeriod :: d.verticalPeriod :: d.cellTypes.map cellCode

def decodeFields : List Nat → Option PeriodicOrthogonalDrawing
  | w::h::rest => do
    if w=0 ∨ h=0 then none else do
      let cells ← rest.mapM decodeCell
      return ⟨w-1,h-1,cells⟩
  | _ => none

private theorem decodeCells (cells : List OrthogonalCellType) :
    (cells.map cellCode).mapM decodeCell = some cells := by
  induction cells with
  | nil => rfl
  | cons k cells ih => simp [ih]

@[simp] theorem decodeFields_fields (d : PeriodicOrthogonalDrawing) :
    decodeFields (fields d) = some d := by
  simp only [fields,decodeFields,horizontalPeriod,verticalPeriod,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,or_self,ite_false,decodeCells,Nat.add_sub_cancel]
  rfl

def finEncoding : _root_.Computability.FinEncoding PeriodicOrthogonalDrawing :=
  PeriodicCNFFlatEncoding.finEncodingOfFields fields decodeFields decodeFields_fields

theorem fields_length (d : PeriodicOrthogonalDrawing) :
    (fields d).length = d.cellTypes.length+2 := by simp [fields,Nat.add_assoc]

end LeanTrominoes.Gadget.NormalizedOrientation.FlatEncoding
end

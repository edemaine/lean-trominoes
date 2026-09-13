/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripArithmeticGeometry
import Mathlib.Tactic.IntervalCases

/-! # Natural bounded quantifiers for the placement-record domains -/

namespace LeanTrominoes.PolyominoStripWindow.Arithmetic
open Raw

def kindOfIndex (index : Nat) : Bool := decide (index = 1)

def symmetryOfIndex : Nat → SquareSymmetry
  | 0 => .identity
  | 1 => .rotate90
  | 2 => .rotate180
  | 3 => .rotate270
  | 4 => .reflectX
  | 5 => .reflectDiagonal
  | 6 => .reflectY
  | _ => .reflectAntidiagonal

theorem symmetryIndex_lt (symmetry : SquareSymmetry) : symmetryIndex symmetry < 8 := by
  cases symmetry <;> decide

@[simp] theorem symmetryOfIndex_index (symmetry : SquareSymmetry) :
    symmetryOfIndex (symmetryIndex symmetry) = symmetry := by cases symmetry <;> rfl

@[simp] theorem symmetryIndex_ofIndex (index : Nat) (hi : index < 8) :
    symmetryIndex (symmetryOfIndex index) = index := by interval_cases index <;> rfl

@[simp] theorem kindOfIndex_toNat (kind : Bool) : kindOfIndex kind.toNat = kind := by cases kind <;> rfl

@[simp] theorem toNat_kindOfIndex (index : Nat) (hi : index < 2) :
    (kindOfIndex index).toNat = index := by interval_cases index <;> rfl

def candidateFields (a : Raw.Candidate) : List Nat :=
  [a.2.2.2,symmetryIndex a.2.2.1,a.2.1.toNat,a.1]

theorem candidateFields_injective : Function.Injective candidateFields := by
  rintro ⟨col,k,s,y⟩ ⟨col',k',s',y'⟩ h
  simp only [candidateFields,List.cons.injEq] at h
  have hs := congrArg symmetryOfIndex h.2.1
  have hk := congrArg kindOfIndex h.2.2.1
  simp only [symmetryOfIndex_index] at hs
  simp only [kindOfIndex_toNat] at hk
  have hy := h.1
  have hc := h.2.2.2.1
  subst col'; subst k'; subst s'; subst y'
  rfl

theorem forall_candidates (height bound : Nat) (p : List Nat → Prop) :
    (∀ column < 2*bound+1, ∀ kind < 2, ∀ symmetry < 8, ∀ y < height+2*bound+1,
      p [y,symmetry,kind,column]) ↔ ∀ a ∈ Raw.keys height bound, p (candidateFields a) := by
  constructor
  · intro h a ha
    have bounds := (Raw.mem_keys a).mp ha
    have hk : a.2.1.toNat < 2 := by cases a.2.1 <;> decide
    exact h a.1 bounds.1 a.2.1.toNat hk (symmetryIndex a.2.2.1) (symmetryIndex_lt _) a.2.2.2 bounds.2
  · intro h column hc kind hk symmetry hs y hy
    let a : Raw.Candidate := (column,kindOfIndex kind,symmetryOfIndex symmetry,y)
    have member : a ∈ Raw.keys height bound := (Raw.mem_keys a).mpr ⟨hc,hy⟩
    simpa [candidateFields,a,symmetryIndex_ofIndex _ hs,toNat_kindOfIndex _ hk] using h a member

theorem exists_candidates (height bound : Nat) (p : List Nat → Prop) :
    (∃ column < 2*bound+1, ∃ kind < 2, ∃ symmetry < 8, ∃ y < height+2*bound+1,
      p [y,symmetry,kind,column]) ↔ ∃ a ∈ Raw.keys height bound, p (candidateFields a) := by
  classical
  have h := forall_candidates height bound (fun fields => ¬ p fields)
  simpa only [not_forall,_root_.not_imp,not_not,exists_prop] using not_congr h

end LeanTrominoes.PolyominoStripWindow.Arithmetic

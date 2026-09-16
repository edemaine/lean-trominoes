/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitPaletteCompiler

/-! # Sparse drawing records as a model of the padded completion source -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Gadget Gadget.PeriodicOrthogonalDrawing LBricks
set_option maxHeartbeats 2000000

abbrev DrawingEntry := Cell × OrthogonalCellType

def natEntry (a : DrawingEntry) : (Nat×Nat)×Nat :=
  ((a.1.1.toNat,a.1.2.toNat+1),(kindIndex (kindOf a.2)).val)

structure SparseModel (d : PeriodicOrthogonalDrawing) (entries : List DrawingEntry) : Prop where
  bounds : ∀ a ∈ entries, 0 ≤ a.1.1 ∧ a.1.1 < d.horizontalPeriod ∧
    0 ≤ a.1.2 ∧ a.1.2 < d.verticalPeriod
  consistent : ∀ a ∈ entries, d.getAt a.1 = a.2
  lookup : ∀ (c : Cell), 0 ≤ c.1 ∧ c.1 < d.horizontalPeriod ∧ 0 ≤ c.2 ∧ c.2 < d.verticalPeriod →
    d.getAt c = (entries.lookup c).getD .blank

private theorem lookup_mem {entries : List DrawingEntry} {c : Cell} {v : OrthogonalCellType}
    (eq : entries.lookup c = some v) : (c,v) ∈ entries := by
  induction entries with
  | nil => simp at eq
  | cons a entries ih =>
    obtain ⟨p,k⟩ := a
    by_cases h : c = p
    · subst p
      simp only [List.lookup_cons,beq_self_eq_true,Option.some.injEq] at eq
      subst k
      simp
    · have beq : (c == p) = false := beq_eq_false_iff_ne.mpr h
      simp only [List.lookup_cons,beq] at eq
      exact List.mem_cons_of_mem _ (ih eq)

theorem SparseModel.natEntry_correct {d : PeriodicOrthogonalDrawing} {entries : List DrawingEntry}
    (model : SparseModel d entries) (a : DrawingEntry) (ha : a ∈ entries) :
    (natEntry a).2 = (kindIndex (stripKinds d ((natEntry a).1.1,(natEntry a).1.2))).val := by
  have bounds := model.bounds a ha
  have x : (a.1.1.toNat:Int) = a.1.1 := by omega
  have y : (a.1.2.toNat:Int) = a.1.2 := by omega
  have inside : 0 ≤ a.1.2 ∧ a.1.2 < d.verticalPeriod := ⟨bounds.2.2.1,bounds.2.2.2⟩
  simp only [natEntry,stripKinds,Circuit.cutKinds,Nat.cast_add,Nat.cast_one,x,y,Int.add_sub_cancel,
    if_pos inside,drawingKinds,model.consistent a ha]

theorem SparseModel.natEntry_support {d : PeriodicOrthogonalDrawing} {entries : List DrawingEntry}
    (model : SparseModel d entries) (x y : Nat) (hx : x < d.horizontalPeriod)
    (missing : ¬ ∃ a ∈ entries, (natEntry a).1 = (x,y)) :
    (kindIndex (stripKinds d ((x:Int),(y:Int)))).val = 0 := by
  by_cases inside : 0 ≤ (y:Int)-1 ∧ (y:Int)-1 < d.verticalPeriod
  · have eq := model.lookup ((x:Int),(y:Int)-1) (by exact ⟨by omega,by dsimp only; exact_mod_cast hx,inside⟩)
    have none : entries.lookup ((x:Int),(y:Int)-1) = none := by
      cases result : entries.lookup ((x:Int),(y:Int)-1) with
      | none => rfl
      | some v =>
        have member := lookup_mem result
        exfalso
        apply missing
        refine ⟨_,member,?_⟩
        simp only [natEntry]
        apply Prod.ext <;> simp <;> omega
    simp only [stripKinds,Circuit.cutKinds,if_pos inside,drawingKinds,eq,none,Option.getD_none]
    rfl
  · simp only [stripKinds,Circuit.cutKinds,if_neg inside]
    rfl
end LeanTrominoes.CompletionPattern.Runtime

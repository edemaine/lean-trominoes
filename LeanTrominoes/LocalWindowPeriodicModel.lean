/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.LocalWindowCycle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-! # Periodic models preserving finite neighborhoods and an integer phase -/
namespace LeanTrominoes.LocalWindow
open Gadget.PeriodicOrthogonalDrawing
set_option maxHeartbeats 1000000

theorem periodic_model {α : Type} [Fintype α] (radius : Nat)
    (valid : Window α radius → Prop) (h : Satisfiable radius valid) :
    ∃ p : Nat, 0 < p ∧ ∃ g : Int → α,
      (∀ x, g (x+p) = g x) ∧ ∀ x, valid (windowAt radius g x) := by
  obtain ⟨m,states,steps⟩ := (satisfiable_iff_cycle radius valid).mp h
  let path : Int → Window α radius := fun x => states (residue x m)
  have step : FiniteState.IsBiInfinitePath (Transition valid) path := by
    intro x; dsimp [path]; rw [residue_add_one]; exact steps _
  refine ⟨m+1,by omega,fun x => path x 0,?_,?_⟩
  · intro x; dsimp [path]
    have eq : residue (x+((m:Int)+1)) m = residue x m := by
      apply Fin.ext; simp [residue,Int.add_emod]
    rw [eq]
  · intro x
    have eq : windowAt radius (fun y => path y 0) x = path x := by
      funext i; exact (path_entry path step i.val i.isLt x).symm
    rw [eq]; exact (step x).1

/-- A periodic sequence can copy each bounded neighborhood of an arbitrary
sequence at a location with the same prescribed phase. -/
theorem periodic_local_copy {α : Type} [Fintype α] (q : Int → α) (r n : Nat) :
    ∃ p : Nat, 0 < p ∧ ∃ g : Int → α,
      (∀ x, g (x+p) = g x) ∧
      ∀ x, ∃ y, ((n+1:Nat):Int) ∣ y-x ∧
        ∀ d : Int, -(r:Int) ≤ d → d ≤ r → g (x+d) = q (y+d) := by
  classical
  let aug : Int → ZMod (n+1) × α := fun x => (x,q x)
  let valid : Window (ZMod (n+1) × α) (2*r+1) → Prop :=
    fun w => ∃ y, w = windowAt (2*r+1) aug y
  obtain ⟨p,hp,g,periodic,hg⟩ := periodic_model (2*r+1) valid ⟨aug,fun x => ⟨x,rfl⟩⟩
  have phaseStep (x : Int) : (g (x+1)).1 = (g x).1+1 := by
    obtain ⟨y,hy⟩ := hg x
    have h0 := congrFun hy (0 : Fin (2*r+1+1))
    have h1 := congrFun hy (1 : Fin (2*r+1+1))
    have bound : 1 < 2*r+1+1 := by omega
    simp only [windowAt,Fin.val_zero,Int.ofNat_zero,add_zero] at h0
    have one : (1 : Fin (2*r+1+1)).val = 1 := by simp [Fin.val_one, Nat.mod_eq_of_lt bound]
    simp only [windowAt,one,Int.ofNat_one] at h1
    rw [h1,h0]; simp [aug]
  have phase (x : Int) : (g x).1 = (x : ZMod (n+1))+(g 0).1 := by
    induction x using Int.induction_on with
    | zero => simp
    | succ x ih => rw [phaseStep,ih]; push_cast; ring
    | pred x ih =>
      have h := phaseStep (-(x:Int)-1)
      rw [sub_add_cancel] at h
      rw [ih] at h
      push_cast at h ⊢
      linear_combination -h
  let s : Int := (g 0).1.val
  have castS : (s : ZMod (n+1)) = (g 0).1 := by simp [s]
  refine ⟨p,hp,fun x => (g (x-s)).2,?_,?_⟩
  · intro x
    dsimp only
    rw [show x+(p:Int)-s = (x-s)+p by ring,periodic]
  · intro x
    obtain ⟨z,hz⟩ := hg (x-s-r)
    have copyAt (d : Int) (lo : -(r:Int) ≤ d) (hi : d ≤ r) :
        g (x-s+d) = aug (z+r+d) := by
      have nn : 0 ≤ d+(r:Int) := by omega
      have bound : (d+(r:Int)).toNat < 2*r+1+1 := by omega
      have hd := congrFun hz ⟨(d+r).toNat,bound⟩
      dsimp [windowAt] at hd
      rw [Int.toNat_of_nonneg nn] at hd
      convert hd using 1 <;> congr 1 <;> ring
    have center := congrArg Prod.fst (copyAt 0 (by omega) (by omega))
    simp only [add_zero,aug] at center
    rw [phase] at center
    have castEq : ((z+(r:Int)-x : Int) : ZMod (n+1)) = 0 := by
      push_cast at center ⊢
      rw [castS] at center
      linear_combination -center
    refine ⟨z+r,?_,?_⟩
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp castEq
    · intro d lo hi
      have h := congrArg Prod.snd (copyAt d lo hi)
      simpa only [aug,show x+d-s = x-s+d by ring] using h
end LeanTrominoes.LocalWindow

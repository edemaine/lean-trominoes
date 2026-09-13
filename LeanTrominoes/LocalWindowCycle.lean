/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteState

/-! # Finite windows for arbitrary one-dimensional local constraints -/

namespace LeanTrominoes.LocalWindow

abbrev Window (α : Type*) (radius : Nat) := Fin (radius+1) → α

def windowAt {α : Type*} (radius : Nat) (configuration : Int → α) (x : Int) : Window α radius :=
  fun i => configuration (x+i.val)

def Transition {α : Type*} {radius : Nat} (valid : Window α radius → Prop)
    (first second : Window α radius) : Prop :=
  valid first ∧ ∀ i : Fin radius, first i.succ = second i.castSucc

def Satisfiable {α : Type*} (radius : Nat) (valid : Window α radius → Prop) : Prop :=
  ∃ configuration : Int → α, ∀ x, valid (windowAt radius configuration x)

theorem path_of_satisfiable {α : Type*} {radius : Nat} {valid : Window α radius → Prop}
    (satisfiable : Satisfiable radius valid) : FiniteState.HasBiInfinitePath (Transition valid) := by
  obtain ⟨configuration,h⟩ := satisfiable
  refine ⟨windowAt radius configuration,fun x => ⟨h x,?_⟩⟩
  intro i
  simp [windowAt]
  congr 1
  omega

/-- Overlap agreement reconstructs every window from its first column. -/
theorem path_entry {α : Type*} {radius : Nat} {valid : Window α radius → Prop}
    (path : Int → Window α radius) (step : FiniteState.IsBiInfinitePath (Transition valid) path)
    (i : Nat) (bound : i < radius+1) (x : Int) :
    path x ⟨i,bound⟩ = path (x+i) 0 := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    have small : i < radius := by omega
    have overlap := (step x).2 ⟨i,small⟩
    change path x ⟨i+1,bound⟩ = path (x+1) ⟨i,by omega⟩ at overlap
    rw [overlap,ih (by omega)]
    congr 1
    push_cast
    omega

theorem satisfiable_of_path {α : Type*} {radius : Nat} {valid : Window α radius → Prop}
    (infinite : FiniteState.HasBiInfinitePath (Transition valid)) : Satisfiable radius valid := by
  obtain ⟨path,step⟩ := infinite
  refine ⟨fun x => path x 0,?_⟩
  intro x
  have eq : windowAt radius (fun x => path x 0) x = path x := by
    funext i
    exact (path_entry path step i.val i.isLt x).symm
  rw [eq]
  exact (step x).1

/-- Local constraints on a finite alphabet admit a global configuration exactly
when their finite overlap graph has a nonempty cycle. -/
theorem satisfiable_iff_cycle {α : Type*} [Fintype α] (radius : Nat)
    (valid : Window α radius → Prop) :
    Satisfiable radius valid ↔ FiniteState.HasCycle (Transition valid) :=
  ⟨fun h => FiniteState.hasCycle_of_hasBiInfinitePath (path_of_satisfiable h),
    fun h => satisfiable_of_path (FiniteState.hasBiInfinitePath_of_hasCycle h)⟩

end LeanTrominoes.LocalWindow

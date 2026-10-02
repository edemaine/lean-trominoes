/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicBipartitionDoubling

/-! # Connectedness cannot be omitted from Lemma 4.4 -/
namespace LeanTrominoes.PeriodicLatticeGraph

def twoStep : List (Arc (Fin 1) 1) := [⟨0,0,fun _ => 2⟩]
def twoStepColor (u : Fin 1 × Lattice 1) : Bool := decide (u.2 0 % 4 < 2)

theorem twoStep_proper : ProperColoring twoStep twoStepColor := by
  intro u v edge
  have displacement : v.2 0=u.2 0+2 ∨ u.2 0=v.2 0+2 := by
    rcases edge with forward | backward
    · obtain ⟨e,he,_,_,equal⟩ := forward
      have same : e=⟨0,0,fun _ => 2⟩ := by simpa [twoStep] using he
      subst e
      exact Or.inl (congrFun equal 0)
    · obtain ⟨e,he,_,_,equal⟩ := backward
      have same : e=⟨0,0,fun _ => 2⟩ := by simpa [twoStep] using he
      subst e
      exact Or.inr (congrFun equal 0)
  by_cases one : u.2 0 % 4 < 2 <;> by_cases two : v.2 0 % 4 < 2
  all_goals simp [twoStepColor,one,two]
  all_goals omega

example : twoStepColor (0,fun _ => 0) ≠ twoStepColor (0,fun _ => 2) := by decide +kernel
example : ¬ Connected twoStep := by
  intro connected
  have same := bipartition_two_periodic twoStep connected twoStepColor twoStep_proper 0 0 (fun _ => 1)
  have ne : twoStepColor (0,fun _ => 0) ≠ twoStepColor (0,fun _ => 2) := by decide +kernel
  exact ne same.symm

end LeanTrominoes.PeriodicLatticeGraph

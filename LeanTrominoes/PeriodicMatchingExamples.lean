/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicMatchingPeriodOne

/-! # Boundary cases for period-one bipartite matching -/
namespace LeanTrominoes.PeriodicBipartite.Examples

-- A single far-offset protoedge tiles the two color classes by pairs.
def distant : List (Edge Unit Unit 3) := [⟨(),(),fun _ => 1000000⟩]
example : HasPerfectMatching distant := by
  apply (perfect_iff_quotient distant).mpr
  refine ⟨Equiv.refl Unit,?_⟩
  intro l
  cases l
  exact ⟨⟨(),(),fun _ => 1000000⟩,by simp [distant],rfl,rfl⟩

-- Unbalanced color classes cannot have a perfect matching, at any offsets.
example (edges : List (Edge (Fin 2) (Fin 1) 3)) : ¬ HasPerfectMatching edges := by
  intro h
  have count := colors_card_eq edges h
  simp at count

-- An isolated orbit on either side rules out a perfect matching.
example : ¬ HasPerfectMatching ([] : List (Edge Unit Unit 1)) := by
  rintro ⟨f,hf⟩
  obtain ⟨e,he,_⟩ := hf ((),0)
  simp at he

-- Empty color classes have the empty period-one matching, including d=0.
example : HasPeriodOneMatching ([] : List (Edge (Fin 0) (Fin 0) 0)) := by
  apply quotient_to_period_one
  exact ⟨Equiv.refl _,fun l => Fin.elim0 l⟩

end LeanTrominoes.PeriodicBipartite.Examples

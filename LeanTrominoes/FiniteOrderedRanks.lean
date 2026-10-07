/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Positive increasing ranks in arbitrary finite linear orders -/
namespace LeanTrominoes

def finiteOrderRank {α : Type*} [LinearOrder α] (values : Finset α) (value : α) : Nat :=
  1+(values.filter fun other => other < value).card

theorem finiteOrderRank_positive {α : Type*} [LinearOrder α] (values : Finset α) (value : α) :
    0 < finiteOrderRank values value := by unfold finiteOrderRank; omega

theorem finiteOrderRank_le_card {α : Type*} [LinearOrder α] {values : Finset α} {value : α}
    (member : value ∈ values) : finiteOrderRank values value ≤ values.card := by
  have proper : values.filter (fun other => other < value) ⊂ values := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro equal
    have inFilter : value ∈ values.filter (fun other => other < value) := by rw [equal]; exact member
    exact (lt_irrefl value) (Finset.mem_filter.mp inFilter).2
  have bound := Finset.card_lt_card proper
  unfold finiteOrderRank
  omega

theorem finiteOrderRank_strictMonoOn {α : Type*} [LinearOrder α] (values : Finset α) :
    StrictMonoOn (finiteOrderRank values) values := by
  intro first fm second _ ordered
  have proper : values.filter (fun other => other < first) ⊂ values.filter (fun other => other < second) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro value member
      have data := Finset.mem_filter.mp member
      exact Finset.mem_filter.mpr ⟨data.1,data.2.trans ordered⟩
    · intro equal
      have inSecond : first ∈ values.filter (fun other => other < second) := Finset.mem_filter.mpr ⟨fm,ordered⟩
      rw [← equal] at inSecond
      exact (lt_irrefl first) (Finset.mem_filter.mp inSecond).2
  have count := Finset.card_lt_card proper
  unfold finiteOrderRank
  omega

end LeanTrominoes

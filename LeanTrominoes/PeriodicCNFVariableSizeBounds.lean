/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Finset.Card

/-! # Presentation size from bounded variable occurrences -/
namespace LeanTrominoes.PeriodicCNF

theorem occurrences_length_le {V : Type*} [DecidableEq V] (f : PeriodicCNF V) (k : Nat)
    (bound : f.OccurrencesAtMost k) : f.variableOccurrences.length ≤ k*f.variableOccurrences.dedup.length := by
  have sumEq := Multiset.toFinset_sum_count_eq (f.variableOccurrences : Multiset V)
  have sumBound := Finset.sum_le_sum (s := (f.variableOccurrences : Multiset V).toFinset)
    (f := fun a => Multiset.count a (f.variableOccurrences : Multiset V)) (g := fun _ => k)
    (fun a _ => by simpa only [Multiset.coe_count] using bound a)
  rw [sumEq] at sumBound
  have cardEq : f.variableOccurrences.toFinset.card = f.variableOccurrences.dedup.length := by
    rw [← List.toFinset_card_of_nodup (List.nodup_dedup f.variableOccurrences)]
    congr 1
    ext a
    simp
  simpa [cardEq,mul_comm] using sumBound

theorem clauses_length_le_literalCount {V : Type*} (f : PeriodicCNF V)
    (nonempty : ∀ c ∈ f.clauses, c ≠ []) : f.clauses.length ≤ f.presentationLiteralCount := by
  rcases f with ⟨clauses⟩
  induction clauses with
  | nil => simp [presentationLiteralCount]
  | cons c cs ih =>
      have hc := List.length_pos_iff.mpr (nonempty c (by simp))
      have tail := ih (fun a ha => nonempty a (by simp [ha]))
      simp only [presentationLiteralCount,List.flatten_cons,List.length_append,List.length_cons]
      change cs.length ≤ cs.flatten.length at tail
      omega

theorem presentationSize_le_variables {V : Type*} [DecidableEq V] (f : PeriodicCNF V)
    (bound : f.OccurrencesAtMost 3) (nonempty : ∀ c ∈ f.clauses, c ≠ []) :
    f.presentationSize ≤ 6*f.variableOccurrences.dedup.length := by
  have literalBound := occurrences_length_le f 3 bound
  rw [variableOccurrences_length] at literalBound
  have clausesBound := clauses_length_le_literalCount f nonempty
  unfold presentationSize
  omega

end LeanTrominoes.PeriodicCNF

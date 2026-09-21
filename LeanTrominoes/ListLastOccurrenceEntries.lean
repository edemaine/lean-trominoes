/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! # Recovering deduplicated vertices from ordered occurrence addresses

Mathlib's `List.dedup` keeps last occurrences. The surviving address records
therefore have exactly the order of the incidence variable vertices.
-/
namespace LeanTrominoes.LastOccurrenceEntries
variable {α : Type} [DecidableEq α]

def survives (entries : List (Nat × α)) (entry : Nat × α) : Prop :=
  ∀ other ∈ entries, entry.1 < other.1 → entry.2 ≠ other.2

instance (entries : List (Nat × α)) (entry : Nat × α) : Decidable (survives entries entry) := by
  unfold survives
  infer_instance

def retained (entries : List (Nat × α)) : List (Nat × α) :=
  entries.filter fun entry => decide (survives entries entry)

theorem retained_cons (first : Nat × α) (rest : List (Nat × α))
    (before : ∀ other ∈ rest, first.1 < other.1) :
    retained (first::rest) = if first.2 ∈ rest.map Prod.snd then retained rest else first::retained rest := by
  have tail : rest.filter (fun entry => decide (survives (first::rest) entry)) = retained rest := by
    apply List.filter_congr
    intro entry he
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    unfold survives
    constructor
    · intro h other ho hl
      exact h other (by simp [ho]) hl
    · intro h other ho hl
      rcases List.mem_cons.mp ho with rfl | ho
      · have lt := before entry he
        omega
      · exact h other ho hl
  have head : survives (first::rest) first ↔ first.2 ∉ rest.map Prod.snd := by
    simp only [survives,List.mem_cons,forall_eq_or_imp,lt_self_iff_false,false_implies,true_and,
      List.mem_map,not_exists,not_and]
    constructor
    · intro h other ho eq
      exact h other ho (before other ho) eq.symm
    · intro h other ho _ eq
      exact h other ho eq.symm
  unfold retained
  rw [List.filter_cons,tail]
  by_cases h : first.2 ∈ rest.map Prod.snd <;> simp [head,h,retained]

theorem map_retained (entries : List (Nat × α))
    (sorted : (entries.map Prod.fst).SortedLT) :
    (retained entries).map Prod.snd = (entries.map Prod.snd).dedup := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
    have pairwise := sorted.pairwise
    simp only [List.map_cons,List.pairwise_cons] at pairwise
    have before : ∀ other ∈ rest, first.1 < other.1 := by
      intro other ho
      exact pairwise.1 other.1 (List.mem_map.mpr ⟨other,ho,rfl⟩)
    rw [retained_cons first rest before]
    have ih' := ih (List.sortedLT_iff_pairwise.mpr pairwise.2)
    by_cases h : first.2 ∈ rest.map Prod.snd <;>
      simp [h,ih']

theorem retained_addresses_nodup (entries : List (Nat × α))
    (sorted : (entries.map Prod.fst).SortedLT) :
    ((retained entries).map Prod.fst).Nodup :=
  sorted.nodup.sublist ((List.filter_sublist (l := entries)).map Prod.fst)

end LeanTrominoes.LastOccurrenceEntries

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicHornCore
import Mathlib.Data.Finset.Card

/-! # A verified finite Horn solver by bounded forward chaining

Each round scans all rules. This implementation is executable but does not
claim the linear-time bound of a worklist implementation.
-/
namespace LeanTrominoes.Horn
variable {V : Type*} [DecidableEq V]

def heads (rules : List (Rule V)) : Finset V := (rules.filterMap Rule.conclusion).toFinset

def step (rules : List (Rule V)) (known : Finset V) : Finset V :=
  known ∪ ((rules.filter (fun r => r.premises.all (fun a => decide (a ∈ known)))).filterMap Rule.conclusion).toFinset

theorem mem_step (rules : List (Rule V)) (known : Finset V) (a : V) :
    a ∈ step rules known ↔ a ∈ known ∨ ∃ r ∈ rules, (∀ b ∈ r.premises, b ∈ known) ∧ r.conclusion=some a := by
  simp [step,List.mem_filterMap,List.mem_filter,List.all_eq_true,and_assoc]

theorem subset_step (rules : List (Rule V)) (known : Finset V) : known ⊆ step rules known := by
  intro a ha
  exact (mem_step rules known a).mpr (Or.inl ha)

theorem step_subset_heads (rules : List (Rule V)) (known : Finset V) (h : known ⊆ heads rules) :
    step rules known ⊆ heads rules := by
  intro a ha
  rcases (mem_step rules known a).mp ha with old | ⟨r,hr,_,head⟩
  · exact h old
  · simpa [heads,List.mem_filterMap] using (show ∃ r ∈ rules, r.conclusion=some a from ⟨r,hr,head⟩)

def run (rules : List (Rule V)) : Nat → Finset V
  | 0 => ∅
  | n+1 => step rules (run rules n)

theorem run_subset_heads (rules : List (Rule V)) (n : Nat) : run rules n ⊆ heads rules := by
  induction n with
  | zero => simp [run]
  | succ n ih => exact step_subset_heads rules _ ih

theorem run_subset_next (rules : List (Rule V)) (n : Nat) : run rules n ⊆ run rules (n+1) :=
  subset_step rules _

theorem stable_or_card (rules : List (Rule V)) (n : Nat) :
    run rules (n+1)=run rules n ∨ n < (run rules (n+1)).card := by
  induction n with
  | zero =>
    by_cases h : run rules 1=run rules 0
    · exact Or.inl h
    · right
      have strict : run rules 0 ⊂ run rules 1 :=
        (ssubset_iff_subset_ne).mpr ⟨run_subset_next rules 0,Ne.symm h⟩
      have bound := Finset.card_lt_card strict
      simpa [run] using bound
  | succ n ih =>
    rcases ih with stable | growth
    · left
      exact congrArg (step rules) stable
    · by_cases stable : run rules (n+2)=run rules (n+1)
      · exact Or.inl stable
      · right
        have strict : run rules (n+1) ⊂ run rules (n+2) :=
          (ssubset_iff_subset_ne).mpr ⟨run_subset_next rules (n+1),Ne.symm stable⟩
        have bound := Finset.card_lt_card strict
        change n+1 < (run rules (n+2)).card
        omega

def closure (rules : List (Rule V)) : Finset V := run rules (heads rules).card

theorem closure_fixed (rules : List (Rule V)) : step rules (closure rules)=closure rules := by
  rcases stable_or_card rules (heads rules).card with stable | growth
  · exact stable
  · have bound := Finset.card_le_card (run_subset_heads rules ((heads rules).card+1))
    omega

theorem run_sound (rules : List (Rule V)) (model : V → Prop) (satisfied : Satisfies rules model)
    (n : Nat) : ∀ a ∈ run rules n, model a := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    intro a ha
    rcases (mem_step rules (run rules n) a).mp ha with old | ⟨r,hr,premises,head⟩
    · exact ih a old
    · have derived := satisfied r hr (fun b hb => ih b (premises b hb))
      simpa [Rule.Holds,head] using derived

def check (rules : List (Rule V)) : Bool :=
  rules.all fun r => match r.conclusion with
    | some _ => true
    | none => !(r.premises.all (fun a => decide (a ∈ closure rules)))

theorem check_iff_model (rules : List (Rule V)) : check rules=true ↔ Satisfies rules (fun a => a ∈ closure rules) := by
  simp only [check,List.all_eq_true,Satisfies]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  cases head : r.conclusion with
  | none => simp [Rule.Holds,head,List.all_eq_true]
  | some a =>
    simp only [Rule.Holds,head,true_iff]
    intro premises
    rw [← closure_fixed rules]
    exact (mem_step rules _ a).mpr (Or.inr ⟨r,hr,premises,head⟩)

theorem check_correct (rules : List (Rule V)) : check rules=true ↔ Satisfiable rules := by
  constructor
  · intro h
    exact ⟨_,(check_iff_model rules).mp h⟩
  · rintro ⟨model,satisfied⟩
    simp only [check,List.all_eq_true]
    intro r hr
    cases head : r.conclusion with
    | some a => rfl
    | none =>
      simp only [Bool.not_eq_true',Bool.eq_false_iff,List.all_eq_true,decide_eq_true_eq]
      intro premises
      simp only [List.all_eq_true,decide_eq_true_eq] at premises
      have contradiction := satisfied r hr (fun a ha => run_sound rules model satisfied _ a (premises a ha))
      simpa [Rule.Holds,head] using contradiction

/-- The returned model is the least model of a satisfiable Horn instance. -/
theorem closure_least (rules : List (Rule V)) (model : V → Prop) (h : Satisfies rules model) :
    ∀ a ∈ closure rules, model a := run_sound rules model h _

end LeanTrominoes.Horn

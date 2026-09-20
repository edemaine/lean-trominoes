/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFLineWindow
import LeanTrominoes.FiniteStateCycleSearch
import LeanTrominoes.PeriodicCNFFlatEncoding

/-! # Executable cycle search for local one-dimensional CNF

The semantic algorithm and its state-size bound are prerequisites for the
encoded TM space certificate; this module does not assert PSPACE membership.
-/
namespace LeanTrominoes.PeriodicCNF.LineWindow
variable {V : Type} [DecidableEq V]

instance (f : PeriodicCNF V) (w : Window f) : Decidable (Valid f w) := by
  unfold Valid
  infer_instance

instance (f : PeriodicCNF V) : DecidableRel (LocalWindow.Transition (Valid f)) := by
  intro first second
  unfold LocalWindow.Transition
  infer_instance

def cycleCheck (f : PeriodicCNF V) : Bool :=
  FiniteState.cycleSearchBool (LocalWindow.Transition (Valid f))

theorem cycleCheck_correct (f : PeriodicCNF V) (horizontal : f.IsOneDimensional)
    (locality : f.IsLocalOnLine) : cycleCheck f = true ↔ f.Satisfiable :=
  (FiniteState.cycleSearchBool_eq_true_iff _).trans (satisfiable_iff_cycle f horizontal locality).symm

private instance localDecidable (f : PeriodicCNF V) : Decidable f.IsLocal := by
  unfold PeriodicCNF.IsLocal PeriodicClause.IsLocal
  infer_instance

def check (f : PeriodicCNF V) : Bool :=
  decide f.IsOneDimensional && decide f.IsLocal && cycleCheck f

theorem check_correct (f : PeriodicCNF V) :
    check f = true ↔ f.IsOneDimensional ∧ f.IsLocal ∧ f.Satisfiable := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨horizontal,locality⟩,cycle⟩
    exact ⟨horizontal,locality,(cycleCheck_correct f horizontal
      ((PeriodicCNF.isLocal_iff_isLocalOnLine horizontal).1 locality)).1 cycle⟩
  · rintro ⟨horizontal,locality,satisfies⟩
    exact ⟨⟨horizontal,locality⟩,(cycleCheck_correct f horizontal
      ((PeriodicCNF.isLocal_iff_isLocalOnLine horizontal).1 locality)).2 satisfies⟩

theorem check_localPeriodicCNF1DSAT (f : PeriodicCNF Nat) :
    check f = true ↔ LocalPeriodicCNF1DSAT f := by
  rw [check_correct]
  unfold LocalPeriodicCNF1DSAT
  apply and_congr_right
  intro horizontal
  exact and_congr (PeriodicCNF.isLocal_iff_isLocalOnLine horizontal)
    (PeriodicCNF.satisfiable_iff_satisfiableOnLine horizontal)

private theorem occurrences_fields (clauses : List (PeriodicClause Nat)) :
    (clauses.flatMap fun c => c.map PeriodicLiteral.atom).length ≤
      (clauses.flatMap PeriodicCNFFlatEncoding.clauseFields).length := by
  induction clauses with
  | nil => simp
  | cons c cs ih =>
    have row : c.length ≤ (PeriodicCNFFlatEncoding.clauseFields c).length := by
      have body : (c.flatMap PeriodicCNFFlatEncoding.literalFields).length = 4*c.length := by
        induction c with
        | nil => simp
        | cons l ls ih => simp [PeriodicCNFFlatEncoding.literalFields,ih]; omega
      simp only [PeriodicCNFFlatEncoding.clauseFields,List.length_cons,body]
      omega
    simp only [List.flatMap_cons,List.length_append,List.length_map]
    omega

/-- There are at most three state bits per symbol of the actual flat input. -/
theorem state_bits_le_encoding (f : PeriodicCNF Nat) :
    3*f.variableOccurrences.length ≤ 3*(PeriodicCNFFlatEncoding.finEncoding.encode f).length := by
  have occurrences : f.variableOccurrences.length ≤ (PeriodicCNFFlatEncoding.formulaFields f).length := by
    have h := occurrences_fields f.clauses
    simp only [PeriodicCNFFlatEncoding.formulaFields,List.length_cons]
    exact h.trans (Nat.le_succ _)
  have fields : ∀ xs : List Nat, xs.length ≤
      (xs.map fun n => (Computability.encodeNat n).length+1).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons n ns ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  rw [PeriodicCNFFlatEncoding.finEncoding_encode_length]
  exact Nat.mul_le_mul_left 3 (occurrences.trans (fields _))
end LeanTrominoes.PeriodicCNF.LineWindow

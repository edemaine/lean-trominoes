/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeComputability
import LeanTrominoes.PeriodicCNFCoRE

/-! # Effective CNF encoding of exact-one constraints -/
namespace LeanTrominoes.PeriodicExactOneCNF
open PeriodicOneInThree

variable {V : Type}

def mutex : PeriodicClause V → List (PeriodicClause V)
  | [] => []
  | l :: ls => ls.map (fun r => [negate l, negate r]) ++ mutex ls

def clause (ls : PeriodicClause V) : List (PeriodicClause V) := ls :: mutex ls

def formula (f : PeriodicCNF V) : PeriodicCNF V :=
  ⟨f.clauses.flatMap clause⟩

private theorem count_zero (values : List Bool) :
    values.count true = 0 ↔ ∀ b ∈ values, b = false := by
  simp only [List.count_eq_zero, List.mem_iff_getElem]
  constructor
  · intro h b hb
    cases b with
    | false => rfl
    | true => exact False.elim (h hb)
  · intro h hb
    have := h true hb
    contradiction

private theorem negate_holds (a : V → Cell → Bool) (c : Cell) (l : PeriodicLiteral V) :
    (negate l).Holds a c ↔ ¬ l.Holds a c := by
  simp only [PeriodicLiteral.Holds, negate]
  cases a l.atom (Cell.add c l.offset) <;> cases l.value <;> decide

theorem mutex_correct (a : V → Cell → Bool) (c : Cell) (ls : PeriodicClause V) :
    (∀ cl ∈ mutex ls, cl.Holds a c) ↔ (clauseValues a c ls).count true ≤ 1 := by
  induction ls with
  | nil => simp [mutex, clauseValues]
  | cons l ls ih =>
    have pair (r : PeriodicLiteral V) :
        PeriodicClause.Holds a c [negate l, negate r] ↔
          ¬ l.Holds a c ∨ ¬ r.Holds a c := by
      simp [PeriodicClause.Holds, negate_holds]
    have zero : (clauseValues a c ls).count true = 0 ↔
        ∀ r ∈ ls, ¬ r.Holds a c := by
      rw [count_zero]
      simp [clauseValues, PeriodicLiteral.Holds]
    simp only [mutex, List.forall_mem_append, List.forall_mem_map, pair, ih,
      clauseValues, List.map_cons, List.count_cons]
    by_cases hl : l.Holds a c
    · have value : (a l.atom (Cell.add c l.offset) == l.value) = true := by
        simpa [PeriodicLiteral.Holds] using hl
      simp only [hl, not_true_eq_false, false_or, value, beq_self_eq_true, ite_true]
      change (∀ r ∈ ls, ¬ r.Holds a c) ∧ (clauseValues a c ls).count true ≤ 1 ↔ _
      rw [← zero]
      change ((clauseValues a c ls).count true = 0 ∧ (clauseValues a c ls).count true ≤ 1) ↔
        (clauseValues a c ls).count true + 1 ≤ 1
      omega
    · have value : (a l.atom (Cell.add c l.offset) == l.value) = false := by
        simpa [PeriodicLiteral.Holds] using hl
      simp [hl, value]

theorem clause_correct (a : V → Cell → Bool) (c : Cell) (ls : PeriodicClause V) :
    (∀ cl ∈ clause ls, cl.Holds a c) ↔ ClauseHolds a c ls := by
  have positive : ls.Holds a c ↔ 0 < (clauseValues a c ls).count true := by
    rw [List.count_pos_iff]
    simp [PeriodicClause.Holds, clauseValues, PeriodicLiteral.Holds]
  simp only [clause, List.forall_mem_cons, mutex_correct, positive,
    ClauseHolds, ExactlyOne]
  omega

theorem satisfies_iff (f : PeriodicCNF V) (a : V → Cell → Bool) :
    (formula f).Satisfies a ↔ Satisfies f a := by
  simp only [PeriodicCNF.Satisfies, formula, List.forall_mem_flatMap, clause_correct,
    Satisfies]

theorem satisfiable_iff (f : PeriodicCNF V) :
    (formula f).Satisfiable ↔ Satisfiable f :=
  exists_congr (satisfies_iff f)

theorem mutex_primrec [Primcodable V] : Primrec (@mutex V) := by
  have pair : Primrec₂ fun (l r : PeriodicLiteral V) => [negate l, negate r] :=
    Primrec.list_cons.comp (negate_primrec.comp Primrec.fst)
      (Primrec.list_cons.comp (negate_primrec.comp Primrec.snd) (Primrec.const []))
  have step : Primrec₂ fun (_ : PeriodicClause V)
      (p : PeriodicLiteral V × PeriodicClause V × List (PeriodicClause V)) =>
      p.2.1.map (fun r => [negate p.1, negate r]) ++ p.2.2 :=
    Primrec.list_append.comp
      (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (pair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  apply (Primrec.list_rec Primrec.id (Primrec.const []) step).of_eq
  intro ls
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simpa only [mutex, id_eq, List.recOn] using congrArg
      (fun rest => ls.map (fun r => [negate l, negate r]) ++ rest) ih

theorem formula_primrec [Primcodable V] : Primrec (@formula V) := by
  have row : Primrec (@clause V) := Primrec.list_cons.comp Primrec.id mutex_primrec
  exact PeriodicCNF.equivData_symm_primrec.comp
    (Primrec.list_flatMap PeriodicCNF.equivData_primrec (row.comp Primrec.snd))

/-- Exact-one satisfiability is co-r.e. for arbitrary finite periodic presentations. -/
theorem satisfiable_coRE [Primcodable V] [DecidableEq V] :
    LeanWang.CoREPred (@PeriodicOneInThree.Satisfiable V) := by
  have upper := LeanWang.REPred.comp (PeriodicCNF.satisfiable_coRE (V := V)) formula_primrec.to_comp
  exact upper.of_eq fun f => not_congr (satisfiable_iff f)

end LeanTrominoes.PeriodicExactOneCNF

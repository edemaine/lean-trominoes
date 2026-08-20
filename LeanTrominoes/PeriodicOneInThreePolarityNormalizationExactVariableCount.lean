/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationOccurrences
import LeanTrominoes.PeriodicSumVariableCount

/-! # Exact distinct-variable count after polarity normalization -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization

open PeriodicCNF

/-- One copy of every distinct occurrence-local fresh variable in a suffix of
the clause presentation. -/
def distinctFreshVariablesFromClauses {Variable : Type*} (start : Nat) :
    List (PeriodicClause Variable) →
      List ((Nat × Nat) × PeriodicLiteral Variable)
  | [] => []
  | clause :: rest =>
      freshVariablesFrom start 0 clause ++
        distinctFreshVariablesFromClauses (start + 1) rest

/-- The actual auxiliary projection contains two occurrences of every fresh
variable: one in the normalized main clause and one in its complement
clause. -/
def repeatedFreshVariablesFromClauses {Variable : Type*} (start : Nat) :
    List (PeriodicClause Variable) →
      List ((Nat × Nat) × PeriodicLiteral Variable)
  | [] => []
  | clause :: rest =>
      (freshVariablesFrom start 0 clause ++
        freshVariablesFrom start 0 clause) ++
          repeatedFreshVariablesFromClauses (start + 1) rest

/-- Every local fresh-variable tag carries its generating clause index. -/
theorem clauseIndex_eq_of_mem_freshVariablesFrom
    {Variable : Type*} (clauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    {fresh : (Nat × Nat) × PeriodicLiteral Variable}
    (member : fresh ∈
      freshVariablesFrom clauseIndex literalStart source) :
    fresh.1.1 = clauseIndex := by
  induction source generalizing literalStart with
  | nil => simp [freshVariablesFrom] at member
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · rw [freshVariablesFrom_cons, if_pos compatible] at member
        exact induction (literalStart + 1) member
      · rw [freshVariablesFrom_cons, if_neg compatible] at member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact induction (literalStart + 1) member

/-- Every fresh tag in a repeated suffix has clause index at least the
suffix's starting index. -/
theorem clauseIndex_ge_of_mem_repeatedFreshVariablesFromClauses
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable))
    {fresh : (Nat × Nat) × PeriodicLiteral Variable}
    (member : fresh ∈
      repeatedFreshVariablesFromClauses start clauses) :
    start ≤ fresh.1.1 := by
  induction clauses generalizing start with
  | nil => simp [repeatedFreshVariablesFromClauses] at member
  | cons clause rest induction =>
      simp only [repeatedFreshVariablesFromClauses,
        List.mem_append] at member
      rcases member with (current | current) | later
      · rw [clauseIndex_eq_of_mem_freshVariablesFrom
          start 0 clause current]
      · rw [clauseIndex_eq_of_mem_freshVariablesFrom
          start 0 clause current]
      · have tail := induction (start + 1) later
        omega

/-- The two current copies are disjoint from every later clause block. -/
theorem current_disjoint_repeatedLater
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (clause : PeriodicClause Variable)
    (rest : List (PeriodicClause Variable)) :
    List.Disjoint
      (freshVariablesFrom start 0 clause ++
        freshVariablesFrom start 0 clause)
      (repeatedFreshVariablesFromClauses (start + 1) rest) := by
  rw [List.disjoint_left]
  intro fresh current later
  simp only [List.mem_append] at current
  have currentIndex : fresh.1.1 = start := by
    rcases current with current | current <;>
      exact clauseIndex_eq_of_mem_freshVariablesFrom
        start 0 clause current
  have laterIndex :=
    clauseIndex_ge_of_mem_repeatedFreshVariablesFromClauses
      (start + 1) rest later
  omega

/-- The complete auxiliary projection is the explicit repeated fresh-variable
stream. -/
theorem formulaClausesFrom_auxiliaryVariables
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    PeriodicOneInThree.auxiliaryVariables
        (PeriodicCNF.variableOccurrences
          ⟨formulaClausesFrom start clauses⟩) =
      repeatedFreshVariablesFromClauses start clauses := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      rw [formulaClausesFrom_cons,
        PeriodicOneInThree.variableOccurrences_append,
        PeriodicOneInThree.SumVariableCount.auxiliaryVariables_append,
        ← clauseClausesFrom_zero start clause,
        clauseClausesFrom_auxiliaryVariables,
        induction (start + 1)]
      rfl

/-- Deduplication removes the second occurrence of every fresh variable and
nothing else. -/
theorem repeatedFreshVariablesFromClauses_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (clauses : List (PeriodicClause Variable)) :
    (repeatedFreshVariablesFromClauses start clauses).dedup.length =
      (distinctFreshVariablesFromClauses start clauses).length := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      let currentFresh := freshVariablesFrom start 0 clause
      have currentFreshNodup : currentFresh.Nodup :=
        freshVariablesFrom_nodup start 0 clause
      have disjoint := current_disjoint_repeatedLater
        start clause rest
      have dedupDouble :
          (currentFresh ++ currentFresh).dedup = currentFresh := by
        rw [List.Subset.dedup_append_right (fun _ member => member),
          List.dedup_eq_self.mpr currentFreshNodup]
      change
        ((currentFresh ++ currentFresh) ++
          repeatedFreshVariablesFromClauses (start + 1) rest).dedup.length =
        (currentFresh ++
          distinctFreshVariablesFromClauses (start + 1) rest).length
      rw [disjoint.dedup_append, dedupDouble,
        List.length_append, induction (start + 1),
        List.length_append]

/-- Fresh-variable counts do not depend on the payload's clause-index tag. -/
theorem freshVariablesFrom_length_clauseIndex
    {Variable : Type*} (firstIndex secondIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (freshVariablesFrom firstIndex literalStart source).length =
      (freshVariablesFrom secondIndex literalStart source).length := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [freshVariablesFrom_cons, compatible,
          induction (literalStart + 1)]
      · simp [freshVariablesFrom_cons, compatible,
          induction (literalStart + 1)]

/-- The length of the one-copy global stream is the sum of the local fresh
occurrence counts. -/
theorem distinctFreshVariablesFromClauses_length
    {Variable : Type*} (start : Nat)
    (clauses : List (PeriodicClause Variable)) :
    (distinctFreshVariablesFromClauses start clauses).length =
      (clauses.map fun clause =>
        (freshVariablesFrom 0 0 clause).length).sum := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest induction =>
      simp only [distinctFreshVariablesFromClauses,
        List.length_append, List.map_cons, List.sum_cons]
      rw [freshVariablesFrom_length_clauseIndex start 0,
        induction (start + 1)]

/-- The original-variable projection has the same distinct cardinality as
the source occurrence list. -/
theorem formula_originalVariables_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicOneInThree.originalVariables
      (PeriodicCNF.variableOccurrences (formula source))).dedup.length =
      source.variableOccurrences.dedup.length := by
  have counts : ∀ atom : Variable,
      (PeriodicOneInThree.originalVariables
        (PeriodicCNF.variableOccurrences (formula source))).count atom =
      source.variableOccurrences.count atom := by
    intro atom
    rw [← PeriodicOneInThree.count_originalVariables]
    exact formula_variableOccurrences_count_original source atom
  have perm :
      (PeriodicOneInThree.originalVariables
          (PeriodicCNF.variableOccurrences (formula source))).Perm
        source.variableOccurrences :=
    List.perm_iff_count.mpr counts
  exact perm.dedup.length_eq

/-- Polarity normalization retains every source variable and adds one
distinct variable per incompatible literal occurrence. -/
theorem formula_variableOccurrences_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      source.variableOccurrences.dedup.length +
        (source.clauses.map fun clause =>
          (freshVariablesFrom 0 0 clause).length).sum := by
  rw [PeriodicOneInThree.SumVariableCount.dedup_length_eq_original_add_auxiliary,
    formula_originalVariables_dedup_length]
  have auxiliaryEq :
      PeriodicOneInThree.auxiliaryVariables
          (PeriodicCNF.variableOccurrences (formula source)) =
        repeatedFreshVariablesFromClauses 0 source.clauses := by
    simpa only [formula, formulaClausesFrom] using
      formulaClausesFrom_auxiliaryVariables 0 source.clauses
  rw [auxiliaryEq,
    repeatedFreshVariablesFromClauses_dedup_length,
    distinctFreshVariablesFromClauses_length]

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes

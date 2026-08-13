/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThree
import Mathlib.Data.Bool.Basic

/-!
# Correctness of periodic 3SAT occurrence splitting

The directed implication cycle makes all copies of a source protovariable
equal at every cell.  This proves that the construction in
`PeriodicThreeSATThree` preserves satisfiability in both directions.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Give every occurrence copy the value of its original protovariable. -/
def extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    ThreeOccurrenceVariable Variable → Cell → Bool :=
  fun occurrence cell => assignment occurrence.1 cell

/-- Read a source protovariable from the first of its occurrence copies,
defaulting to false only when it never occurs. -/
def restrictAssignment {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell =>
    ((occurrenceVariables source atom).head?.map fun occurrence =>
      assignment occurrence cell).getD false

@[simp]
theorem occurrenceLiteral_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable) :
    (occurrenceLiteral clauseIndex literalIndex literal).Holds
        (extendAssignment assignment) translate ↔
      literal.Holds assignment translate := by
  rfl

theorem implicationClause_holds_iff {Variable : Type*}
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (cell : Cell) (first second : ThreeOccurrenceVariable Variable) :
    (implicationClause first second).Holds assignment cell ↔
      assignment first cell ≤ assignment second cell := by
  simp only [implicationClause, PeriodicClause.Holds, List.mem_cons,
    List.not_mem_nil, or_false, PeriodicLiteral.Holds, Cell.add,
    Bool.le_iff_imp]
  cases firstValue : assignment first cell <;>
    cases secondValue : assignment second cell <;>
    simp [firstValue, secondValue]

theorem cycleFrom_current_le_first {Variable : Type*}
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (cell : Cell) (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (satisfies : ∀ clause ∈ cycleFrom first current rest,
      clause.Holds assignment cell) :
    assignment current cell ≤ assignment first cell := by
  induction rest generalizing current with
  | nil =>
      exact (implicationClause_holds_iff assignment cell current first).1
        (satisfies (implicationClause current first) (by simp [cycleFrom]))
  | cons next rest induction =>
      have current_le_next :
          assignment current cell ≤ assignment next cell :=
        (implicationClause_holds_iff assignment cell current next).1
          (satisfies (implicationClause current next) (by simp [cycleFrom]))
      have tailSatisfies :
          ∀ clause ∈ cycleFrom first next rest,
            clause.Holds assignment cell := by
        intro clause clause_mem
        exact satisfies clause (by simp [cycleFrom, clause_mem])
      exact current_le_next.trans (induction next tailSatisfies)

theorem cycleFrom_each_le_first {Variable : Type*}
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (cell : Cell) (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (satisfies : ∀ clause ∈ cycleFrom first current rest,
      clause.Holds assignment cell) :
    ∀ copy ∈ current :: rest,
      assignment copy cell ≤ assignment first cell := by
  induction rest generalizing current with
  | nil =>
      intro copy copy_mem
      have copy_eq := List.mem_singleton.mp copy_mem
      subst copy
      exact cycleFrom_current_le_first assignment cell first current []
        satisfies
  | cons next rest induction =>
      intro copy copy_mem
      rcases List.mem_cons.mp copy_mem with copy_eq | copy_mem
      · subst copy
        exact cycleFrom_current_le_first assignment cell first current
          (next :: rest) satisfies
      · have tailSatisfies :
            ∀ clause ∈ cycleFrom first next rest,
              clause.Holds assignment cell := by
          intro clause clause_mem
          exact satisfies clause (by simp [cycleFrom, clause_mem])
        exact induction next tailSatisfies copy copy_mem

theorem cycleFrom_root_le_each {Variable : Type*}
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (cell : Cell) (root first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (root_le_current : assignment root cell ≤ assignment current cell)
    (satisfies : ∀ clause ∈ cycleFrom first current rest,
      clause.Holds assignment cell) :
    ∀ copy ∈ current :: rest,
      assignment root cell ≤ assignment copy cell := by
  induction rest generalizing current with
  | nil =>
      intro copy copy_mem
      have copy_eq := List.mem_singleton.mp copy_mem
      subst copy
      exact root_le_current
  | cons next rest induction =>
      intro copy copy_mem
      rcases List.mem_cons.mp copy_mem with copy_eq | copy_mem
      · subst copy
        exact root_le_current
      · have current_le_next :
            assignment current cell ≤ assignment next cell :=
          (implicationClause_holds_iff assignment cell current next).1
            (satisfies (implicationClause current next) (by simp [cycleFrom]))
        have tailSatisfies :
            ∀ clause ∈ cycleFrom first next rest,
              clause.Holds assignment cell := by
          intro clause clause_mem
          exact satisfies clause (by simp [cycleFrom, clause_mem])
        exact induction next (root_le_current.trans current_le_next)
          tailSatisfies copy copy_mem

/-- Every copy in a satisfied implication cycle has the first copy's value. -/
theorem cycleClauses_value_eq_first {Variable : Type*}
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (cell : Cell) (first : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (satisfies : ∀ clause ∈ cycleClauses (first :: rest),
      clause.Holds assignment cell) :
    ∀ copy ∈ first :: rest,
      assignment copy cell = assignment first cell := by
  have cycleSatisfies :
      ∀ clause ∈ cycleFrom first first rest,
        clause.Holds assignment cell := by
    simpa [cycleClauses] using satisfies
  have each_le := cycleFrom_each_le_first assignment cell first first rest
    cycleSatisfies
  have first_le := cycleFrom_root_le_each assignment cell first first first rest
    (le_refl _) cycleSatisfies
  intro copy copy_mem
  exact le_antisymm (each_le copy copy_mem) (first_le copy copy_mem)

theorem occurrenceVariables_fst {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) {copy : ThreeOccurrenceVariable Variable}
    (copy_mem : copy ∈ occurrenceVariables source atom) :
    copy.1 = atom := by
  simp only [occurrenceVariables, List.mem_filterMap] at copy_mem
  rcases copy_mem with ⟨tagged, tagged_mem, selected⟩
  split at selected
  · simp only [Option.some.injEq] at selected
    subst copy
    rfl
  · contradiction

theorem implicationClause_holds_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (first second : ThreeOccurrenceVariable Variable)
    (sameOriginal : first.1 = second.1) :
    (implicationClause first second).Holds
      (extendAssignment assignment) cell := by
  rw [implicationClause_holds_iff]
  simp only [extendAssignment]
  rw [sameOriginal]

theorem cycleFrom_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (atom : Variable)
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (firstOriginal : first.1 = atom)
    (currentOriginal : current.1 = atom)
    (restOriginal : ∀ copy ∈ rest, copy.1 = atom) :
    ∀ clause ∈ cycleFrom first current rest,
      clause.Holds (extendAssignment assignment) cell := by
  induction rest generalizing current with
  | nil =>
      intro clause clause_mem
      simp only [cycleFrom, List.mem_singleton] at clause_mem
      subst clause
      exact implicationClause_holds_extend assignment cell current first
        (currentOriginal.trans firstOriginal.symm)
  | cons next rest induction =>
      intro clause clause_mem
      simp only [cycleFrom, List.mem_cons] at clause_mem
      rcases clause_mem with rfl | clause_mem
      · exact implicationClause_holds_extend assignment cell current next
          (currentOriginal.trans (restOriginal next (by simp)).symm)
      · exact induction next (restOriginal next (by simp))
          (fun copy copy_mem => restOriginal copy (by simp [copy_mem]))
          clause clause_mem

theorem cycleClauses_complete {Variable : Type*}
    [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (atom : Variable) :
    ∀ clause ∈ cycleClauses (occurrenceVariables source atom),
      clause.Holds (extendAssignment assignment) cell := by
  cases copies_eq : occurrenceVariables source atom with
  | nil => simp [cycleClauses]
  | cons first rest =>
      have firstOriginal : first.1 = atom :=
        occurrenceVariables_fst source atom
          (copies_eq ▸ List.mem_cons_self)
      have restOriginal : ∀ copy ∈ rest, copy.1 = atom := by
        intro copy copy_mem
        exact occurrenceVariables_fst source atom
          (copies_eq ▸ List.mem_cons_of_mem first copy_mem)
      simpa [copies_eq, cycleClauses] using
        cycleFrom_complete assignment cell atom first first rest
          firstOriginal firstOriginal restOriginal

theorem taggedLiterals_mem {Variable : Type*}
    (source : PeriodicCNF Variable)
    {taggedClause : PeriodicClause Variable × Nat}
    (clause_mem : taggedClause ∈ source.clauses.zipIdx)
    {taggedLiteral : PeriodicLiteral Variable × Nat}
    (literal_mem : taggedLiteral ∈ taggedClause.1.zipIdx) :
    (taggedLiteral.1, taggedClause.2, taggedLiteral.2) ∈
      taggedLiterals source := by
  simp only [taggedLiterals, List.mem_flatMap, List.mem_map]
  exact ⟨taggedClause, clause_mem,
    ⟨taggedLiteral, literal_mem, rfl⟩⟩

theorem occurrenceVariables_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    {literal : PeriodicLiteral Variable} {clauseIndex literalIndex : Nat}
    (tagged_mem : (literal, clauseIndex, literalIndex) ∈
      taggedLiterals source) :
    (literal.atom, clauseIndex, literalIndex) ∈
      occurrenceVariables source literal.atom := by
  simp only [occurrenceVariables, List.mem_filterMap]
  exact ⟨(literal, clauseIndex, literalIndex), tagged_mem, by simp⟩

theorem sourceVariables_mem {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    {literal : PeriodicLiteral Variable} {clauseIndex literalIndex : Nat}
    (tagged_mem : (literal, clauseIndex, literalIndex) ∈
      taggedLiterals source) :
    literal.atom ∈ sourceVariables source := by
  simp only [sourceVariables, List.mem_dedup, List.mem_map]
  exact ⟨(literal, clauseIndex, literalIndex), tagged_mem, rfl⟩

theorem occurrenceClause_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (sourceHolds : clause.Holds assignment translate) :
    (occurrenceClause clauseIndex clause).Holds
      (extendAssignment assignment) translate := by
  rcases sourceHolds with ⟨literal, literal_mem, literal_holds⟩
  have mapped_mem :
      literal ∈ clause.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using literal_mem
  rcases List.mem_map.mp mapped_mem with
    ⟨⟨taggedLiteral, literalIndex⟩, tagged_mem, tagged_eq⟩
  simp only at tagged_eq
  subst taggedLiteral
  refine ⟨occurrenceLiteral clauseIndex literalIndex literal, ?_,
    (occurrenceLiteral_holds_extend assignment translate clauseIndex
      literalIndex literal).2 literal_holds⟩
  simp only [occurrenceClause, List.mem_map]
  exact ⟨(literal, literalIndex), tagged_mem, rfl⟩

/-- Extending a source assignment satisfies both the copied source clauses and
all implication cycles. -/
theorem formula_satisfies_of_satisfies {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (satisfies : source.Satisfies assignment) :
    (formula source).Satisfies (extendAssignment assignment) := by
  intro translate clause clause_mem
  simp only [formula, List.mem_append] at clause_mem
  rcases clause_mem with source_mem | cycle_mem
  · simp only [occurrenceClauses, List.mem_map] at source_mem
    rcases source_mem with ⟨taggedClause, taggedClause_mem, rfl⟩
    exact occurrenceClause_complete assignment translate taggedClause.2
      taggedClause.1
      (satisfies translate taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClause_mem))
  · simp only [allCycleClauses, List.mem_flatMap] at cycle_mem
    rcases cycle_mem with ⟨atom, atom_mem, cycle_mem⟩
    exact cycleClauses_complete source assignment translate atom
      clause cycle_mem

theorem restrictAssignment_eq_copy {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies : (formula source).Satisfies assignment)
    (atom : Variable) (atom_mem : atom ∈ sourceVariables source)
    (cell : Cell) (copy : ThreeOccurrenceVariable Variable)
    (copy_mem : copy ∈ occurrenceVariables source atom) :
    restrictAssignment source assignment atom cell =
      assignment copy cell := by
  cases copies_eq : occurrenceVariables source atom with
  | nil =>
      simp [copies_eq] at copy_mem
  | cons first rest =>
      have cycleSatisfies :
          ∀ clause ∈ cycleClauses (first :: rest),
            clause.Holds assignment cell := by
        intro clause clause_mem
        apply satisfies cell clause
        simp only [formula, List.mem_append]
        apply Or.inr
        simp only [allCycleClauses, List.mem_flatMap]
        exact ⟨atom, atom_mem, by simpa [copies_eq] using clause_mem⟩
      have copy_eq_first :=
        cycleClauses_value_eq_first assignment cell first rest
          cycleSatisfies copy (by simpa [copies_eq] using copy_mem)
      simp only [restrictAssignment, copies_eq, List.head?_cons,
        Option.map_some, Option.getD_some]
      exact copy_eq_first.symm

theorem occurrenceLiteral_holds_restrict {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies : (formula source).Satisfies assignment)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable)
    (tagged_mem : (literal, clauseIndex, literalIndex) ∈
      taggedLiterals source) :
    (occurrenceLiteral clauseIndex literalIndex literal).Holds
        assignment translate ↔
      literal.Holds (restrictAssignment source assignment) translate := by
  have atom_mem := sourceVariables_mem source tagged_mem
  have copy_mem := occurrenceVariables_mem source tagged_mem
  have values_eq := restrictAssignment_eq_copy source assignment satisfies
    literal.atom atom_mem (Cell.add translate literal.offset)
    (literal.atom, clauseIndex, literalIndex) copy_mem
  simp only [PeriodicLiteral.Holds, occurrenceLiteral]
  rw [values_eq]

/-- Restricting a satisfying occurrence assignment satisfies every original
source clause. -/
theorem satisfies_of_formula_satisfies {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies : (formula source).Satisfies assignment) :
    source.Satisfies (restrictAssignment source assignment) := by
  intro translate clause clause_mem
  have mapped_mem :
      clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clause_mem
  rcases List.mem_map.mp mapped_mem with
    ⟨⟨taggedClause, clauseIndex⟩, taggedClause_mem, taggedClause_eq⟩
  simp only at taggedClause_eq
  subst taggedClause
  have occurrenceHolds :
      (occurrenceClause clauseIndex clause).Holds assignment translate := by
    apply satisfies translate (occurrenceClause clauseIndex clause)
    simp only [formula, List.mem_append]
    apply Or.inl
    simp only [occurrenceClauses, List.mem_map]
    exact ⟨(clause, clauseIndex), taggedClause_mem, rfl⟩
  rcases occurrenceHolds with
    ⟨copiedLiteral, copiedLiteral_mem, copiedLiteral_holds⟩
  simp only [occurrenceClause, List.mem_map] at copiedLiteral_mem
  rcases copiedLiteral_mem with
    ⟨⟨literal, literalIndex⟩, taggedLiteral_mem, rfl⟩
  refine ⟨literal, List.fst_mem_of_mem_zipIdx taggedLiteral_mem, ?_⟩
  apply (occurrenceLiteral_holds_restrict source assignment satisfies
    translate clauseIndex literalIndex literal ?_).1
  · exact copiedLiteral_holds
  · exact taggedLiterals_mem source taggedClause_mem taggedLiteral_mem

/-- The standard periodic occurrence split preserves satisfiability exactly. -/
theorem satisfiable_iff {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    source.Satisfiable ↔ (formula source).Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨extendAssignment assignment,
      formula_satisfies_of_satisfies source assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨restrictAssignment source assignment,
      satisfies_of_formula_satisfies source assignment satisfies⟩

end PeriodicThreeSATThree
end LeanTrominoes

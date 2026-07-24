import LeanTrominoes.PeriodicThreeCNF
import Mathlib.Data.List.Enum

/-!
# Reduction of periodic 3SAT to periodic 3SAT-3

This file implements the cycle construction from Theorem 3.4.  Every literal
occurrence gets its own protovariable.  For each original protovariable, binary
implication clauses connect its occurrence copies in a directed cycle.

The implication literals use a common offset.  Because every protoclauses is
imposed at every lattice translate, this forces the copies to agree at every
cell even when their source occurrences used different offsets.
-/

namespace LeanTrominoes

/-- A copy of an original variable identified by its clause and literal
positions in the finite periodic presentation. -/
abbrev ThreeOccurrenceVariable (Variable : Type*) :=
  Variable × Nat × Nat

namespace PeriodicThreeSATThree

/-- All source literals tagged with their clause and literal positions. -/
def taggedLiterals {Variable : Type*} (source : PeriodicCNF Variable) :
    List (PeriodicLiteral Variable × Nat × Nat) :=
  source.clauses.zipIdx.flatMap fun (clause, clauseIndex) =>
    clause.zipIdx.map fun (literal, literalIndex) =>
      (literal, clauseIndex, literalIndex)

/-- The original protovariables that actually occur in the presentation, in
order of first occurrence. -/
def sourceVariables {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Variable :=
  (taggedLiterals source).map (fun tagged => tagged.1.atom) |>.eraseDups

/-- The occurrence copies belonging to one original protovariable. -/
def occurrenceVariables {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  (taggedLiterals source).filterMap fun tagged =>
    if tagged.1.atom = atom then
      some (atom, tagged.2.1, tagged.2.2)
    else
      none

/-- Replace a source literal by the copy at its syntactic occurrence. -/
def occurrenceLiteral {Variable : Type*}
    (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable) :
    PeriodicLiteral (ThreeOccurrenceVariable Variable) :=
  ⟨(literal.atom, clauseIndex, literalIndex), literal.offset, literal.value⟩

/-- Replace every literal of a source clause by its occurrence copy. -/
def occurrenceClause {Variable : Type*} (clauseIndex : Nat)
    (clause : PeriodicClause Variable) :
    PeriodicClause (ThreeOccurrenceVariable Variable) :=
  clause.zipIdx.map fun (literal, literalIndex) =>
    occurrenceLiteral clauseIndex literalIndex literal

/-- The source clauses with every literal occurrence split apart. -/
def occurrenceClauses {Variable : Type*} (source : PeriodicCNF Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  source.clauses.zipIdx.map fun (clause, clauseIndex) =>
    occurrenceClause clauseIndex clause

/-- The binary clause expressing `first → second`, aligned at one common
offset so it compares the two copies at the same cell. -/
def implicationClause {Variable : Type*}
    (first second : ThreeOccurrenceVariable Variable) :
    PeriodicClause (ThreeOccurrenceVariable Variable) :=
  [⟨first, (0, 0), false⟩, ⟨second, (0, 0), true⟩]

/-- Complete a directed implication path by closing it back to `first`. -/
def cycleFrom {Variable : Type*}
    (first : ThreeOccurrenceVariable Variable) :
    ThreeOccurrenceVariable Variable →
      List (ThreeOccurrenceVariable Variable) →
        List (PeriodicClause (ThreeOccurrenceVariable Variable))
  | current, [] => [implicationClause current first]
  | current, next :: rest =>
      implicationClause current next :: cycleFrom first next rest

/-- A directed implication cycle through all copies. -/
def cycleClauses {Variable : Type*} :
    List (ThreeOccurrenceVariable Variable) →
      List (PeriodicClause (ThreeOccurrenceVariable Variable))
  | [] => []
  | first :: rest => cycleFrom first first rest

/-- All implication cycles, one for each original variable. -/
def allCycleClauses {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  (sourceVariables source).flatMap fun atom =>
    cycleClauses (occurrenceVariables source atom)

/-- The standard occurrence-splitting reduction from periodic 3SAT to
periodic 3SAT-3. -/
def formula {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF (ThreeOccurrenceVariable Variable) where
  clauses := occurrenceClauses source ++ allCycleClauses source

theorem occurrenceClause_length {Variable : Type*}
    (clauseIndex : Nat) (clause : PeriodicClause Variable) :
    (occurrenceClause clauseIndex clause).length = clause.length := by
  simp [occurrenceClause]

theorem occurrenceLiteral_offsetDistance {Variable : Type*}
    (firstClauseIndex firstLiteralIndex secondClauseIndex
      secondLiteralIndex : Nat)
    (first second : PeriodicLiteral Variable) :
    PeriodicClause.offsetDistance
        (occurrenceLiteral firstClauseIndex firstLiteralIndex first)
        (occurrenceLiteral secondClauseIndex secondLiteralIndex second) =
      PeriodicClause.offsetDistance first second := by
  rfl

theorem occurrenceClause_isLocal {Variable : Type*}
    (clauseIndex : Nat) {clause : PeriodicClause Variable}
    (sourceLocal : clause.IsLocal) :
    (occurrenceClause clauseIndex clause).IsLocal := by
  intro first first_mem second second_mem
  simp only [occurrenceClause, List.mem_map] at first_mem second_mem
  rcases first_mem with ⟨firstTagged, firstTagged_mem, rfl⟩
  rcases second_mem with ⟨secondTagged, secondTagged_mem, rfl⟩
  rw [occurrenceLiteral_offsetDistance]
  exact sourceLocal firstTagged.1
    (List.fst_mem_of_mem_zipIdx firstTagged_mem)
    secondTagged.1 (List.fst_mem_of_mem_zipIdx secondTagged_mem)

theorem implicationClause_isLocal {Variable : Type*}
    (first second : ThreeOccurrenceVariable Variable) :
    (implicationClause first second).IsLocal := by
  simp [PeriodicClause.IsLocal, PeriodicClause.offsetDistance,
    implicationClause]

theorem cycleFrom_areLocal {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleFrom first current rest, clause.IsLocal := by
  induction rest generalizing current with
  | nil =>
      simpa [cycleFrom] using implicationClause_isLocal current first
  | cons next rest induction =>
      intro clause clause_mem
      simp only [cycleFrom, List.mem_cons] at clause_mem
      rcases clause_mem with rfl | clause_mem
      · exact implicationClause_isLocal current next
      · exact induction next clause clause_mem

theorem cycleClauses_areLocal {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleClauses copies, clause.IsLocal := by
  cases copies with
  | nil => simp [cycleClauses]
  | cons first rest =>
      exact cycleFrom_areLocal first first rest

/-- Occurrence splitting preserves the paper's locality condition. -/
theorem formula_isLocal {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable} (sourceLocal : source.IsLocal) :
    (formula source).IsLocal := by
  intro clause clause_mem
  simp only [formula, List.mem_append] at clause_mem
  rcases clause_mem with source_mem | cycle_mem
  · simp only [occurrenceClauses, List.mem_map] at source_mem
    rcases source_mem with ⟨taggedClause, taggedClause_mem, rfl⟩
    exact occurrenceClause_isLocal taggedClause.2
      (sourceLocal taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClause_mem))
  · simp only [allCycleClauses, List.mem_flatMap] at cycle_mem
    rcases cycle_mem with ⟨atom, atom_mem, cycle_mem⟩
    exact cycleClauses_areLocal (occurrenceVariables source atom)
      clause cycle_mem

theorem implicationClause_widthAtMostThree {Variable : Type*}
    (first second : ThreeOccurrenceVariable Variable) :
    (implicationClause first second).WidthAtMost 3 := by
  simp [PeriodicClause.WidthAtMost, implicationClause]

theorem cycleFrom_widthAtMostThree {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleFrom first current rest, clause.WidthAtMost 3 := by
  induction rest generalizing current with
  | nil =>
      simpa [cycleFrom] using
        implicationClause_widthAtMostThree current first
  | cons next rest induction =>
      intro clause clause_mem
      simp only [cycleFrom, List.mem_cons] at clause_mem
      rcases clause_mem with rfl | clause_mem
      · exact implicationClause_widthAtMostThree current next
      · exact induction next clause clause_mem

theorem cycleClauses_widthAtMostThree {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleClauses copies, clause.WidthAtMost 3 := by
  cases copies with
  | nil => simp [cycleClauses]
  | cons first rest =>
      exact cycleFrom_widthAtMostThree first first rest

/-- Occurrence splitting preserves a width-three bound. -/
theorem formula_widthAtMostThree {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable} (width : source.WidthAtMost 3) :
    (formula source).WidthAtMost 3 := by
  intro clause clause_mem
  simp only [formula, List.mem_append] at clause_mem
  rcases clause_mem with source_mem | cycle_mem
  · simp only [occurrenceClauses, List.mem_map] at source_mem
    rcases source_mem with ⟨taggedClause, taggedClause_mem, rfl⟩
    rw [PeriodicClause.WidthAtMost, occurrenceClause_length]
    exact width taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClause_mem)
  · simp only [allCycleClauses, List.mem_flatMap] at cycle_mem
    rcases cycle_mem with ⟨atom, atom_mem, cycle_mem⟩
    exact cycleClauses_widthAtMostThree
      (occurrenceVariables source atom) clause cycle_mem

end PeriodicThreeSATThree
end LeanTrominoes

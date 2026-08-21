/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeCNFForwardLocal
import LeanTrominoes.PeriodicThreeSATThree

/-! # Forward-locality of periodic occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

theorem occurrenceLiteral_isForwardLocal
    {Variable : Type*} (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable)
    (forward : literal.IsForwardLocal) :
    (occurrenceLiteral clauseIndex literalIndex literal).IsForwardLocal := by
  simpa [occurrenceLiteral, PeriodicLiteral.IsForwardLocal] using forward

theorem occurrenceClause_isForwardLocal
    {Variable : Type*} (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (forward : ∀ literal ∈ clause, literal.IsForwardLocal) :
    ∀ literal ∈ occurrenceClause clauseIndex clause,
      literal.IsForwardLocal := by
  intro literal literalMember
  simp only [occurrenceClause, List.mem_map] at literalMember
  rcases literalMember with ⟨tagged, taggedMember, rfl⟩
  exact occurrenceLiteral_isForwardLocal
    clauseIndex tagged.2 tagged.1
      (forward tagged.1
        (List.fst_mem_of_mem_zipIdx taggedMember))

theorem implicationClause_isForwardLocal
    {Variable : Type*}
    (first second : ThreeOccurrenceVariable Variable) :
    ∀ literal ∈ implicationClause first second,
      literal.IsForwardLocal := by
  simp [implicationClause, PeriodicLiteral.IsForwardLocal]

theorem cycleFrom_areForwardLocal
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleFrom first current rest,
      ∀ literal ∈ clause, literal.IsForwardLocal := by
  induction rest generalizing current with
  | nil =>
      intro clause clauseMember
      simp only [cycleFrom, List.mem_singleton] at clauseMember
      subst clause
      exact implicationClause_isForwardLocal current first
  | cons next rest induction =>
      intro clause clauseMember
      simp only [cycleFrom, List.mem_cons] at clauseMember
      rcases clauseMember with rfl | clauseMember
      · exact implicationClause_isForwardLocal current next
      · exact induction next clause clauseMember

theorem cycleClauses_areForwardLocal
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleClauses copies,
      ∀ literal ∈ clause, literal.IsForwardLocal := by
  cases copies with
  | nil => simp [cycleClauses]
  | cons first rest =>
      exact cycleFrom_areForwardLocal first first rest

/-- Occurrence splitting preserves the current/next-slice fragment. -/
theorem formula_isForwardLocal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceForward : source.IsForwardLocal) :
    (formula source).IsForwardLocal := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at occurrenceMember
    rcases occurrenceMember with ⟨tagged, taggedMember, rfl⟩
    exact occurrenceClause_isForwardLocal tagged.2 tagged.1
      (sourceForward tagged.1
        (List.fst_mem_of_mem_zipIdx taggedMember))
      literal literalMember
  · simp only [allCycleClauses, List.mem_flatMap] at cycleMember
    rcases cycleMember with ⟨atom, atomMember, cycleMember⟩
    exact cycleClauses_areForwardLocal
      (occurrenceVariables source atom)
      clause cycleMember literal literalMember

end PeriodicThreeSATThree
end LeanTrominoes

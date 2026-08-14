/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripOneDimensional
import LeanTrominoes.PeriodicEightOccurrenceSplit

/-!
# One-dimensional fixed-eight occurrence splitting

Occurrence copies retain their source literal offsets.  The fixed nine-copy
implication ring uses only offset zero, so every choice of compass ports
preserves the one-dimensional fragment.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A fixed-port occurrence clause inherits zero vertical offsets from its
source clause. -/
theorem occurrenceClause_isOneDimensional
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ literal ∈ occurrenceClause occurrencePorts clauseIndex source,
      literal.offset.2 = 0 := by
  intro literal literalMember
  simp only [occurrenceClause, List.mem_map] at literalMember
  obtain ⟨tagged, taggedMember, rfl⟩ := literalMember
  simpa [occurrenceLiteral] using
    horizontal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)

/-- Every implication clause in one fixed ring has zero vertical offsets. -/
theorem cycleClausesFor_isOneDimensional
    {Variable : Type*} (atom : Variable) :
    ∀ clause ∈ cycleClausesFor atom,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  exact PeriodicThreeSATThree.cycleClauses_isOneDimensional (copies atom)

/-- All fixed implication rings have zero vertical offsets. -/
theorem allCycleClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ∀ clause ∈ allCycleClauses source,
      ∀ literal ∈ clause, literal.offset.2 = 0 := by
  intro clause clauseMember literal literalMember
  simp only [allCycleClauses, List.mem_flatMap] at clauseMember
  obtain ⟨atom, _atomMember, clauseMember⟩ := clauseMember
  exact cycleClausesFor_isOneDimensional atom
    clause clauseMember literal literalMember

/-- Fixed-eight occurrence splitting preserves one-dimensionality for every
compass-port assignment. -/
theorem formula_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (occurrencePorts : OccurrencePorts)
    (horizontal : source.IsOneDimensional) :
    (formula source occurrencePorts).IsOneDimensional := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at occurrenceMember
    obtain ⟨taggedClause, taggedClauseMember, rfl⟩ := occurrenceMember
    exact occurrenceClause_isOneDimensional occurrencePorts
      taggedClause.2 taggedClause.1
      (horizontal taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember))
      literal literalMember
  · exact allCycleClauses_isOneDimensional source
      clause cycleMember literal literalMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes

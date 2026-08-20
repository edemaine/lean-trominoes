/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Exact distinct-variable count after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

theorem cycleFrom_variableOccurrences_subset {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    PeriodicCNF.variableOccurrences ⟨cycleFrom first current rest⟩ ⊆
      first :: current :: rest := by
  induction rest generalizing current with
  | nil =>
      intro copy member
      simp only [cycleFrom, PeriodicCNF.variableOccurrences,
        implicationClause, List.flatMap_cons, List.flatMap_nil,
        List.map_cons, List.map_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
  | cons next rest induction =>
      intro copy member
      rw [show cycleFrom first current (next :: rest) =
          [implicationClause current next] ++
            cycleFrom first next rest by rfl,
        variableOccurrences_append, List.mem_append] at member
      rcases member with currentMember | laterMember
      · simp only [PeriodicCNF.variableOccurrences, implicationClause,
          List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          List.append_nil, List.mem_cons, List.not_mem_nil,
          or_false] at currentMember
        simp only [List.mem_cons]
        rcases currentMember with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · have later := induction next laterMember
        simp only [List.mem_cons] at later ⊢
        rcases later with firstEqual | nextEqual | restMember
        · exact Or.inl firstEqual
        · exact Or.inr (Or.inr (Or.inl nextEqual))
        · exact Or.inr (Or.inr (Or.inr restMember))

theorem cycleClauses_variableOccurrences_subset {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    PeriodicCNF.variableOccurrences ⟨cycleClauses copies⟩ ⊆ copies := by
  cases copies with
  | nil => simp [cycleClauses, PeriodicCNF.variableOccurrences]
  | cons first rest =>
      intro copy member
      have contained := cycleFrom_variableOccurrences_subset
        first first rest member
      simpa [cycleClauses] using contained

theorem variableOccurrences_flatMap {Index Variable : Type*}
    (indices : List Index)
    (clauses : Index →
      List (PeriodicClause (ThreeOccurrenceVariable Variable))) :
    PeriodicCNF.variableOccurrences ⟨indices.flatMap clauses⟩ =
      indices.flatMap fun index =>
        PeriodicCNF.variableOccurrences ⟨clauses index⟩ := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      rw [List.flatMap_cons,
        variableOccurrences_append (clauses index)
          (indices.flatMap clauses),
        List.flatMap_cons, induction]

/-- Cycle clauses introduce no variables beyond the positional occurrence
copies already present in the copied source clauses. -/
theorem allCycleClauses_variableOccurrences_subset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.variableOccurrences ⟨allCycleClauses source⟩ ⊆
      allOccurrenceVariables source := by
  intro copy member
  unfold allCycleClauses at member
  rw [variableOccurrences_flatMap, List.mem_flatMap] at member
  obtain ⟨atom, atomMember, copyMember⟩ := member
  have inOccurrences :=
    cycleClauses_variableOccurrences_subset
      (occurrenceVariables source atom) copyMember
  rw [occurrenceVariables_eq_filter] at inOccurrences
  exact List.mem_of_mem_filter inOccurrences

/-- Every source literal receives one distinct positional variable, and the
cycle clauses add no new variables. -/
@[simp] theorem formula_variableOccurrences_dedup_length
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.variableOccurrences (formula source)).dedup.length =
      PeriodicCNF.presentationLiteralCount source := by
  let originals := allOccurrenceVariables source
  let cycles :=
    PeriodicCNF.variableOccurrences ⟨allCycleClauses source⟩
  have formulaOccurrences :
      PeriodicCNF.variableOccurrences (formula source) =
        originals ++ cycles := by
    unfold formula originals cycles
    rw [variableOccurrences_append,
      occurrenceClauses_variableOccurrences]
  have cyclesSubset : cycles ⊆ originals := by
    exact allCycleClauses_variableOccurrences_subset source
  have sameMembers : ∀ copy,
      copy ∈ (originals ++ cycles).dedup ↔ copy ∈ originals := by
    intro copy
    rw [List.mem_dedup, List.mem_append]
    constructor
    · rintro (inOriginals | inCycles)
      · exact inOriginals
      · exact cyclesSubset inCycles
    · exact Or.inl
  have perm : (originals ++ cycles).dedup.Perm originals :=
    (List.perm_ext_iff_of_nodup
      (List.nodup_dedup _) (allOccurrenceVariables_nodup source)).mpr
        sameMembers
  rw [formulaOccurrences]
  calc
    (originals ++ cycles).dedup.length = originals.length :=
      perm.length_eq
    _ = (taggedLiterals source).length := by
      simp [originals, allOccurrenceVariables]
    _ = PeriodicCNF.presentationLiteralCount source :=
      taggedLiterals_length source

end PeriodicThreeSATThree
end LeanTrominoes

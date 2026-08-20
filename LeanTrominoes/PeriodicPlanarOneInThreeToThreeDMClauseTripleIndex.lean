/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncode

/-! # Stable indices in the typed clause-triple suffix -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- Numbering typed triples preserves the triple-list length. -/
@[simp] theorem encodedProblem_triples_length
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (encodedProblem source).triples.length = (triples source).length := by
  simp [encodedProblem, TypedProblem.encode, problem]

/-- Rebase a zero-based `zipIdx` member at an arbitrary start. -/
private theorem mem_zipIdx_from
    {α : Type*} (start : Nat) (values : List α)
    {value : α} {index : Nat}
    (member : (value, index) ∈ values.zipIdx) :
    (value, start + index) ∈ values.zipIdx start := by
  rw [List.zipIdx_eq_map_add]
  exact List.mem_map.mpr ⟨(value, index), member, rfl⟩

/-- The local set index in a nine-triple clause block gives its global index
after the variable-triple prefix. -/
theorem clauseTriple_mem_triples_zipIdx
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clauseIndexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet) (setIndex : Nat)
    (setMember : (set, setIndex) ∈ allClauseSets.zipIdx) :
    (Triple.clause clauseIndex set,
      (variableTriples source).length + 9 * clauseIndex + setIndex) ∈
      (triples source).zipIdx := by
  unfold triples
  rw [List.zipIdx_append]
  apply List.mem_append.mpr
  right
  unfold clauseTriples
  simp only [Nat.zero_add]
  change
    (Triple.clause clauseIndex set,
      (variableTriples source).length + 9 * clauseIndex + setIndex) ∈
      ((List.range source.clauses.length).flatMap fun index =>
        allClauseSets.map fun localSet =>
          (Triple.clause index localSet : Triple Variable)).zipIdx
        (variableTriples source).length
  rw [IndexedListScan.range_flatMap_zipIdx_eq_flatMap_zipIdx_fixed
    (Output := Triple Variable)
    source.clauses.length
    (fun index => allClauseSets.map fun localSet =>
      (Triple.clause index localSet : Triple Variable))
    9 (variableTriples source).length
    (by intro index; simp [allClauseSets])]
  apply List.mem_flatMap.mpr
  refine ⟨clauseIndex, List.mem_range.mpr clauseIndexLt, ?_⟩
  have shifted := mem_zipIdx_from
    ((variableTriples source).length + 9 * clauseIndex)
    allClauseSets setMember
  rw [List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨(set, (variableTriples source).length +
      9 * clauseIndex + setIndex), shifted, rfl⟩

/-- Optional lookup form of `clauseTriple_mem_triples_zipIdx`. -/
theorem clauseTriple_getElem?
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clauseIndexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet) (setIndex : Nat)
    (setMember : (set, setIndex) ∈ allClauseSets.zipIdx) :
    (triples source)[(variableTriples source).length +
      9 * clauseIndex + setIndex]? =
      some (.clause clauseIndex set) := by
  exact (List.mem_zipIdx_iff_getElem?).mp
    (clauseTriple_mem_triples_zipIdx source clauseIndex clauseIndexLt
      set setIndex setMember)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

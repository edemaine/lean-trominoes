/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraph
import Mathlib.Data.List.Range

/-! # Exact vertex indices in periodic-CNF incidence graphs -/

namespace LeanTrominoes

namespace List

/-- An injective map preserves the first-occurrence index of a mapped
element. -/
theorem idxOf_map_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (function : α → β) (injective : Function.Injective function)
    (values : List α) (value : α) :
    (values.map function).idxOf (function value) = values.idxOf value := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases same : head = value
      · subst head
        simp
      · have mappedNe : function head ≠ function value :=
          fun equal => same (injective equal)
        simp [same, mappedNe, induction]

end List

namespace PeriodicCNF

/-- An occurring variable vertex has exactly its position in the deduplicated
variable-occurrence prefix. -/
theorem incidenceGraph_variable_vertexIndex
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable)
    (atomMember : atom ∈ formula.variableOccurrences.dedup) :
    formula.incidenceGraph.vertices.idxOf (CNFVertex.variable atom) =
      formula.variableOccurrences.dedup.idxOf atom := by
  unfold incidenceGraph incidenceVariableVertices incidenceClauseVertices
  rw [List.idxOf_append_of_mem]
  · exact List.idxOf_map_of_injective CNFVertex.variable
      (fun _ _ equal => by cases equal; rfl) _ atom
  · exact List.mem_map.mpr ⟨atom, atomMember, rfl⟩

/-- Clause vertices form the suffix immediately following all distinct
variable vertices. -/
theorem incidenceGraph_clause_vertexIndex
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (clauseIndex : Nat)
    (clauseIndexLt : clauseIndex < formula.clauses.length) :
    formula.incidenceGraph.vertices.idxOf (CNFVertex.clause clauseIndex) =
      formula.variableOccurrences.dedup.length + clauseIndex := by
  unfold incidenceGraph incidenceVariableVertices incidenceClauseVertices
  rw [List.idxOf_append_of_notMem]
  · simp only [List.length_map]
    congr 1
    rw [List.idxOf_map_of_injective CNFVertex.clause
      (fun _ _ equal => by cases equal; rfl)]
    have indexLtRange :
        clauseIndex < (List.range formula.clauses.length).length := by
      simpa using clauseIndexLt
    have elementEq :
        (List.range formula.clauses.length)[clauseIndex] = clauseIndex :=
      List.getElem_range indexLtRange
    calc
      (List.range formula.clauses.length).idxOf clauseIndex =
          (List.range formula.clauses.length).idxOf
            (List.range formula.clauses.length)[clauseIndex] := by
              rw [elementEq]
      _ = clauseIndex :=
        (List.nodup_range :
          (List.range formula.clauses.length).Nodup).idxOf_getElem
            clauseIndex indexLtRange
  · simp

end PeriodicCNF
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorData

/-! # Presentation facts for numeric CNF route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

theorem metadataIncidence_clauseIndex_lt
    {Variable : Type*} (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember : tagged ∈ (incidencesWithMetadata formula).zipIdx) :
    tagged.1.clauseIndex < formula.clauses.length := by
  have incidenceMember : tagged.1 ∈ incidencesWithMetadata formula :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have members :=
    (mem_incidencesWithMetadata_iff formula tagged.1).mp incidenceMember
  exact List.snd_lt_of_mem_zipIdx members.1

theorem metadataIncidence_atom_mem_variableOccurrences
    {Variable : Type*} (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember : tagged ∈ (incidencesWithMetadata formula).zipIdx) :
    tagged.1.literal.atom ∈ formula.variableOccurrences := by
  have incidenceMember : tagged.1 ∈ incidencesWithMetadata formula :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have members :=
    (mem_incidencesWithMetadata_iff formula tagged.1).mp incidenceMember
  unfold variableOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨tagged.1.clause,
    List.fst_mem_of_mem_zipIdx members.1, ?_⟩
  exact List.mem_map.mpr
    ⟨tagged.1.literal,
      List.fst_mem_of_mem_zipIdx members.2, rfl⟩

theorem metadataIncidence_atom_mem_dedup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember : tagged ∈ (incidencesWithMetadata formula).zipIdx) :
    tagged.1.literal.atom ∈ formula.variableOccurrences.dedup := by
  rw [List.mem_dedup]
  exact metadataIncidence_atom_mem_variableOccurrences
    formula tagged taggedMember

@[simp] theorem incidenceGraph_vertices_length_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    formula.incidenceGraph.vertices.length =
      formula.variableOccurrences.dedup.length + formula.clauses.length := by
  unfold incidenceGraph incidenceVariableVertices incidenceClauseVertices
  simp

@[simp] theorem incidenceGraph_edges_length_eq_metadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    formula.incidenceGraph.edges.length =
      (incidencesWithMetadata formula).length := by
  have lengths := congrArg List.length
    (incidencesWithMetadata_edges formula)
  simpa using lengths.symm

end PeriodicCNF
end LeanTrominoes

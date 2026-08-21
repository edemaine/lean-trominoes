/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapFixedTake
import LeanTrominoes.PeriodicCNFPlanarIncidences
import LeanTrominoes.PeriodicOrthocrossingPortRankIncidencePrefix

/-! # CNF incidence port ranks from metadata prefixes -/

namespace LeanTrominoes

namespace CNFIncidence

/-- The source clause vertex followed by the target variable vertex of one
metadata-rich CNF incidence. -/
def vertexBlock {Variable : Type*} (incidence : CNFIncidence Variable) :
    List (CNFVertex Variable) :=
  [.clause incidence.clauseIndex, .variable incidence.literal.atom]

@[simp] theorem vertexBlock_length
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    incidence.vertexBlock.length = 2 := rfl

theorem vertexBlocks_count_clause
    {Variable : Type*} [DecidableEq Variable]
    (incidences : List (CNFIncidence Variable)) (clauseIndex : Nat) :
    (incidences.flatMap vertexBlock).count (.clause clauseIndex) =
      (incidences.map CNFIncidence.clauseIndex).count clauseIndex := by
  induction incidences with
  | nil => rfl
  | cons incidence incidences induction =>
      rw [List.flatMap_cons, List.map_cons, List.count_append]
      by_cases same : incidence.clauseIndex = clauseIndex
      · subst clauseIndex
        rw [List.count_cons_self]
        have blockCount :
            incidence.vertexBlock.count
              (.clause incidence.clauseIndex) = 1 := by
          simp [vertexBlock]
        rw [blockCount, induction]
        omega
      · rw [List.count_cons_of_ne same]
        have blockCount :
            incidence.vertexBlock.count (.clause clauseIndex) = 0 := by
          simp [vertexBlock, same]
        rw [blockCount, zero_add, induction]

theorem vertexBlocks_count_variable
    {Variable : Type*} [DecidableEq Variable]
    (incidences : List (CNFIncidence Variable)) (atom : Variable) :
    (incidences.flatMap vertexBlock).count (.variable atom) =
      (incidences.map fun incidence => incidence.literal.atom).count atom := by
  induction incidences with
  | nil => rfl
  | cons incidence incidences induction =>
      rw [List.flatMap_cons, List.map_cons, List.count_append]
      by_cases same : incidence.literal.atom = atom
      · subst atom
        rw [List.count_cons_self]
        have blockCount :
            incidence.vertexBlock.count
              (.variable incidence.literal.atom) = 1 := by
          simp [vertexBlock]
        rw [blockCount, induction]
        omega
      · rw [List.count_cons_of_ne same]
        have blockCount :
            incidence.vertexBlock.count (.variable atom) = 0 := by
          simp [vertexBlock, same]
        rw [blockCount, zero_add, induction]

end CNFIncidence

namespace PeriodicCNF

/-- The graph-theoretic incidence stream is the metadata stream with each
literal expanded to its clause and variable endpoints. -/
theorem incidenceGraph_incidences_eq_metadataVertexBlocks
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    formula.incidenceGraph.incidences =
      (incidencesWithMetadata formula).flatMap CNFIncidence.vertexBlock := by
  unfold PeriodicGraph.incidences
  rw [← incidencesWithMetadata_edges, List.flatMap_map]
  rfl

end PeriodicCNF

namespace PeriodicOrthocrossing

/-- A CNF clause-side port rank counts prior metadata incidences from the
same clause. -/
theorem incidenceSourcePortRank_eq_priorClauseCount
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidencesWithMetadata formula).zipIdx) :
    portRank formula.incidenceGraph
        (sourcePort tagged.1.edge tagged.2) =
      (((PeriodicCNF.incidencesWithMetadata formula).take tagged.2).map
        CNFIncidence.clauseIndex).count tagged.1.clauseIndex := by
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem formula taggedMember
  rw [sourcePortRank_eq_incidencePrefixCount
      formula.incidenceGraph (tagged.1.edge, tagged.2) edgeMember,
    PeriodicCNF.incidenceGraph_incidences_eq_metadataVertexBlocks]
  have lookup := (List.mem_zipIdx_iff_getElem?).mp taggedMember
  rw [show 2 * tagged.2 = 2 * tagged.2 + 0 by omega,
    List.take_mul_add_flatMap_of_getElem?
      (PeriodicCNF.incidencesWithMetadata formula)
      CNFIncidence.vertexBlock 2 CNFIncidence.vertexBlock_length
      tagged.1 tagged.2 0 lookup (by omega)]
  simp only [List.take_zero, List.append_nil]
  exact CNFIncidence.vertexBlocks_count_clause _ _

/-- A CNF variable-side port rank counts prior metadata occurrences of the
same variable.  The current edge's source endpoint is a clause vertex and so
does not affect this count. -/
theorem incidenceTargetPortRank_eq_priorAtomCount
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidencesWithMetadata formula).zipIdx) :
    portRank formula.incidenceGraph
        (targetPort tagged.1.edge tagged.2) =
      (((PeriodicCNF.incidencesWithMetadata formula).take tagged.2).map
        fun incidence => incidence.literal.atom).count
          tagged.1.literal.atom := by
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem formula taggedMember
  rw [targetPortRank_eq_incidencePrefixCount
      formula.incidenceGraph (tagged.1.edge, tagged.2) edgeMember,
    PeriodicCNF.incidenceGraph_incidences_eq_metadataVertexBlocks]
  have lookup := (List.mem_zipIdx_iff_getElem?).mp taggedMember
  rw [List.take_mul_add_flatMap_of_getElem?
    (PeriodicCNF.incidencesWithMetadata formula)
    CNFIncidence.vertexBlock 2 CNFIncidence.vertexBlock_length
    tagged.1 tagged.2 1 lookup (by omega)]
  change
    (((PeriodicCNF.incidencesWithMetadata formula).take tagged.2 |>.flatMap
        CNFIncidence.vertexBlock) ++ tagged.1.vertexBlock.take 1).count
          (.variable tagged.1.literal.atom) = _
  rw [List.count_append,
    CNFIncidence.vertexBlocks_count_variable]
  simp [CNFIncidence.vertexBlock]

end PeriodicOrthocrossing
end LeanTrominoes

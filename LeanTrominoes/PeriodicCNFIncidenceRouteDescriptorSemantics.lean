/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorFacts

/-! # Correctness of numeric CNF route descriptors -/

namespace LeanTrominoes
namespace CNFIncidence

/-- Every listed metadata incidence's compact numeric descriptor is exactly
the descriptor extracted from its semantic incidence graph edge. -/
theorem routeDescriptor_eq_numericRouteDescriptor
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidencesWithMetadata formula).zipIdx) :
    PeriodicOrthocrossing.routeDescriptor
        formula.incidenceGraph tagged.1.edge tagged.2 =
      tagged.1.numericRouteDescriptor formula tagged.2 := by
  have clauseIndexLt :=
    PeriodicCNF.metadataIncidence_clauseIndex_lt
      formula tagged taggedMember
  have atomMember :=
    PeriodicCNF.metadataIncidence_atom_mem_dedup
      formula tagged taggedMember
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem formula taggedMember
  unfold PeriodicOrthocrossing.routeDescriptor numericRouteDescriptor
  congr 1
  · exact PeriodicCNF.incidenceGraph_vertices_length_eq formula
  · exact PeriodicCNF.incidenceGraph_edges_length_eq_metadata formula
  · simpa using PeriodicCNF.incidenceGraph_clause_vertexIndex
      formula tagged.1.clauseIndex clauseIndexLt
  · simpa using PeriodicCNF.incidenceGraph_variable_vertexIndex
      formula tagged.1.literal.atom atomMember
  · exact PeriodicOrthocrossing.incidenceSourcePortRank_eq_priorClauseCount
      formula tagged taggedMember
  · exact
      PeriodicOrthocrossing.incidenceTargetPortRank_eq_variableOccurrencePrefixCount
        formula tagged taggedMember

end CNFIncidence
end LeanTrominoes

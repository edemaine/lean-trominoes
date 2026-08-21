/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceHorizontalOffsets
import LeanTrominoes.PeriodicCNFIncidencePortOrder

/-! # Per-incidence route segment count -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem taggedIncidence_route_segments_length
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal)
    (degree : (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (tagged : PeriodicEdge (CNFVertex Variable) × Nat)
    (taggedMember :
      tagged ∈ (PeriodicCNF.incidenceGraph formula).edges.zipIdx) :
    (gridPolylineSegments
      (constructedEdgeRoute
        (PeriodicCNF.incidenceGraph formula)
        tagged.1 tagged.2)).length =
      5 + portSegmentExtra
          (portRank (PeriodicCNF.incidenceGraph formula)
            (sourcePort tagged.1 tagged.2)) +
        portSegmentExtra
          (portRank (PeriodicCNF.incidenceGraph formula)
            (targetPort tagged.1 tagged.2)) +
        backwardCoreSegmentExtra tagged.1.offset := by
  rcases tagged with ⟨edge, edgeIndex⟩
  have edgeMember :
      edge ∈ (PeriodicCNF.incidenceGraph formula).edges :=
    List.fst_mem_of_mem_zipIdx taggedMember
  simp only [PeriodicCNF.incidenceGraph, List.mem_flatMap]
      at edgeMember
  rcases edgeMember with
    ⟨taggedClause, taggedClauseMember, edgeMember⟩
  simp only [PeriodicCNF.clauseIncidenceEdges, List.mem_map]
      at edgeMember
  rcases edgeMember with ⟨literal, literalMember, edgeEq⟩
  subst edge
  have clauseForward :=
    forward taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  have horizontal :=
    PeriodicCNF.incidenceEdge_offset_zero_right_or_left_of_forward
      taggedClause.2 taggedClause.1 literal literalMember clauseForward
  have targetLtSource := incidencePort_target_lt_source
    formula taggedClause.2
      (PeriodicCNF.clauseAnchor taggedClause.1)
      literal edgeIndex taggedMember degree
  exact constructedEdgeRoute_segments_length_horizontal
    (PeriodicCNF.incidenceGraph formula)
    (PeriodicCNF.incidenceEdge taggedClause.2
      (PeriodicCNF.clauseAnchor taggedClause.1) literal)
    edgeIndex horizontal targetLtSource

end PeriodicOrthocrossing
end LeanTrominoes

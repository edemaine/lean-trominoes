/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicGraph

/-!
# Horizontal periodic graphs

A periodic graph is horizontal when none of its prototype edges changes the
vertical lattice translate.  This is the graph-level invariant needed to cut
a one-dimensional periodic construction along a vertical seam.
-/

namespace LeanTrominoes

namespace PeriodicGraph

/-- Every lifted edge stays in one horizontal row of fundamental domains. -/
def HasZeroVerticalOffsets {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : Prop :=
  ∀ edge ∈ graph.edges, edge.offset.2 = 0

end PeriodicGraph

namespace PeriodicCNF

/-- The incidence graph of a one-dimensional periodic CNF is horizontal.
Clause anchoring merely subtracts the vertical-zero offset of the first
literal. -/
theorem incidenceGraph_hasZeroVerticalOffsets {Variable : Type*}
    [DecidableEq Variable] {formula : PeriodicCNF Variable}
    (horizontal : formula.IsOneDimensional) :
    (incidenceGraph formula).HasZeroVerticalOffsets := by
  intro edge edgeMember
  simp only [incidenceGraph, List.mem_flatMap] at edgeMember
  obtain ⟨taggedClause, taggedClauseMember, edgeMember⟩ := edgeMember
  have clauseMember : taggedClause.1 ∈ formula.clauses :=
    List.fst_mem_of_mem_zipIdx taggedClauseMember
  simp only [clauseIncidenceEdges, List.mem_map] at edgeMember
  obtain ⟨literal, literalMember, rfl⟩ := edgeMember
  have literalVertical :=
    horizontal taggedClause.1 clauseMember literal literalMember
  cases clauseEq : taggedClause.1 with
  | nil => simp [clauseEq] at literalMember
  | cons first rest =>
      have firstVertical :=
        horizontal (first :: rest) (by simpa [clauseEq] using clauseMember)
          first (by simp)
      simp [incidenceEdge, clauseAnchor, Cell.sub,
        literalVertical, firstVertical]

end PeriodicCNF
end LeanTrominoes

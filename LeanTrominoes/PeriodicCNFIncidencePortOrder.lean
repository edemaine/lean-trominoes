/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingHorizontalRouteSegmentCount
import LeanTrominoes.PeriodicOrthocrossingPorts

/-! # Left-to-right order of CNF incidence ports

The incidence presentation lists all variable vertices before all clause
vertices.  The eight-column spacing between vertex blocks dominates the
three possible port offsets, so every genuine variable port lies strictly
left of its corresponding clause port.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem incidencePort_target_lt_source
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat) (anchor : Cell)
    (literal : PeriodicLiteral Variable) (edgeIndex : Nat)
    (taggedMember :
      (PeriodicCNF.incidenceEdge clauseIndex anchor literal, edgeIndex) ∈
        (PeriodicCNF.incidenceGraph formula).edges.zipIdx)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3) :
    portX (PeriodicCNF.incidenceGraph formula)
        (targetPort
          (PeriodicCNF.incidenceEdge clauseIndex anchor literal)
          edgeIndex) <
      portX (PeriodicCNF.incidenceGraph formula)
        (sourcePort
          (PeriodicCNF.incidenceEdge clauseIndex anchor literal)
          edgeIndex) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let edge := PeriodicCNF.incidenceEdge clauseIndex anchor literal
  have edgeMember : edge ∈ graph.edges :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have endpoints :=
    (PeriodicCNF.incidenceGraph_isWellFormed formula).2 edge edgeMember
  have targetVariableMember :
      CNFVertex.variable literal.atom ∈
        PeriodicCNF.incidenceVariableVertices formula := by
    have targetMember := endpoints.2
    change CNFVertex.variable literal.atom ∈ graph.vertices at targetMember
    rw [show graph.vertices =
        PeriodicCNF.incidenceVariableVertices formula ++
          PeriodicCNF.incidenceClauseVertices formula by rfl,
      List.mem_append] at targetMember
    rcases targetMember with variableMember | clauseMember
    · exact variableMember
    · simp [PeriodicCNF.incidenceClauseVertices] at clauseMember
  have sourceNotVariable :
      CNFVertex.clause clauseIndex ∉
        PeriodicCNF.incidenceVariableVertices formula := by
    simp [PeriodicCNF.incidenceVariableVertices]
  have targetIndexLt :
      graph.vertices.idxOf (CNFVertex.variable literal.atom) <
        (PeriodicCNF.incidenceVariableVertices formula).length := by
    rw [show graph.vertices =
        PeriodicCNF.incidenceVariableVertices formula ++
          PeriodicCNF.incidenceClauseVertices formula by rfl,
      List.idxOf_append_of_mem targetVariableMember]
    exact List.idxOf_lt_length_iff.mpr targetVariableMember
  have sourceIndexGe :
      (PeriodicCNF.incidenceVariableVertices formula).length ≤
        graph.vertices.idxOf (CNFVertex.clause clauseIndex) := by
    rw [show graph.vertices =
        PeriodicCNF.incidenceVariableVertices formula ++
          PeriodicCNF.incidenceClauseVertices formula by rfl,
      List.idxOf_append_of_notMem sourceNotVariable]
    omega
  have sourceRankLt :
      portRank graph (sourcePort edge edgeIndex) < 3 :=
    portRank_lt_three degree
      (sourcePort_mem_allPorts graph taggedMember)
  have targetRankLt :
      portRank graph (targetPort edge edgeIndex) < 3 :=
    portRank_lt_three degree
      (targetPort_mem_allPorts graph taggedMember)
  change portX graph (targetPort edge edgeIndex) <
    portX graph (sourcePort edge edgeIndex)
  unfold portX vertexX
  change
    8 * (graph.vertices.idxOf (CNFVertex.variable literal.atom) : Int) +
          4 + 2 * (portRank graph (targetPort edge edgeIndex) : Int) - 2 <
      8 * (graph.vertices.idxOf (CNFVertex.clause clauseIndex) : Int) +
          4 + 2 * (portRank graph (sourcePort edge edgeIndex) : Int) - 2
  omega

end PeriodicOrthocrossing
end LeanTrominoes

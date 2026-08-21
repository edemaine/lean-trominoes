/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceClausePortSegmentExtraSum

/-! # Total fanout extras for periodic CNF incidence graphs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem incidenceVariableVertices_portSegmentExtra_sum_of_count_eq_three
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (exact : ∀ atom ∈ formula.variableOccurrences.dedup,
      formula.variableOccurrences.count atom = 3) :
    ((PeriodicCNF.incidenceVariableVertices formula).map fun vertex =>
      portSegmentExtrasForDegree
        (portsAt (PeriodicCNF.incidenceGraph formula) vertex).length).sum =
      2 * formula.variableOccurrences.dedup.length := by
  let graph := PeriodicCNF.incidenceGraph formula
  change ((formula.variableOccurrences.dedup.map CNFVertex.variable).map
      (fun vertex => portSegmentExtrasForDegree
        (portsAt graph vertex).length)).sum = _
  rw [List.map_map]
  have mappedEq :
      formula.variableOccurrences.dedup.map
          ((fun vertex => portSegmentExtrasForDegree
            (portsAt graph vertex).length) ∘ CNFVertex.variable) =
        List.replicate formula.variableOccurrences.dedup.length 2 := by
    calc
      _ = formula.variableOccurrences.dedup.map (fun _ => 2) := by
        apply List.map_congr_left
        intro atom atomMember
        change portSegmentExtrasForDegree
          (portsAt graph (CNFVertex.variable atom)).length = 2
        rw [portsAt_length,
          PeriodicCNF.incidenceGraph_variable_degree,
          exact atom atomMember]
        rfl
      _ = List.replicate formula.variableOccurrences.dedup.length 2 := by
        simp
  rw [mappedEq]
  simp [Nat.mul_comm]

/-- When every represented variable occurs exactly three times, the total
endpoint fanout contribution is the clause-degree scan plus two per distinct
variable. -/
theorem incidenceGraph_portSegmentExtra_sum_of_count_eq_three
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (exact : ∀ atom ∈ formula.variableOccurrences.dedup,
      formula.variableOccurrences.count atom = 3) :
    ((PeriodicCNF.incidenceGraph formula).edges.zipIdx.map fun tagged =>
      portSegmentExtra
          (portRank (PeriodicCNF.incidenceGraph formula)
            (sourcePort tagged.1 tagged.2)) +
        portSegmentExtra
          (portRank (PeriodicCNF.incidenceGraph formula)
            (targetPort tagged.1 tagged.2))).sum =
      (formula.clauses.map fun clause =>
          portSegmentExtrasForDegree clause.length).sum +
        2 * formula.variableOccurrences.dedup.length := by
  let graph := PeriodicCNF.incidenceGraph formula
  rw [← allPorts_portSegmentExtra_sum_eq_edges graph]
  rw [allPorts_portSegmentExtra_sum_eq_vertices
    (PeriodicCNF.incidenceGraph_isWellFormed formula)]
  change ((PeriodicCNF.incidenceVariableVertices formula ++
      PeriodicCNF.incidenceClauseVertices formula).map fun vertex =>
        portSegmentExtrasForDegree (portsAt graph vertex).length).sum = _
  rw [List.map_append, List.sum_append,
    incidenceVariableVertices_portSegmentExtra_sum_of_count_eq_three
      formula exact,
    incidenceClauseVertices_portSegmentExtra_sum formula]
  omega

end PeriodicOrthocrossing
end LeanTrominoes

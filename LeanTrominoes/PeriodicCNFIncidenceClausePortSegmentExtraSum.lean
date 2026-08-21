/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceClauseDegreeExact
import LeanTrominoes.PeriodicOrthocrossingPortSegmentExtraSum

/-! # Clause-side fanout extras for periodic CNF incidence graphs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem incidenceClauseVertices_portSegmentExtra_sum
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((PeriodicCNF.incidenceClauseVertices formula).map fun vertex =>
      portSegmentExtrasForDegree
        (portsAt (PeriodicCNF.incidenceGraph formula) vertex).length).sum =
      (formula.clauses.map fun clause =>
        portSegmentExtrasForDegree clause.length).sum := by
  let graph := PeriodicCNF.incidenceGraph formula
  change ((PeriodicCNF.incidenceClauseVertices formula).map fun vertex =>
      portSegmentExtrasForDegree (portsAt graph vertex).length).sum = _
  unfold PeriodicCNF.incidenceClauseVertices
  rw [show List.range formula.clauses.length =
      formula.clauses.zipIdx.map Prod.snd by
    rw [List.zipIdx_map_snd, List.range_eq_range']]
  simp only [List.map_map, Function.comp_def]
  calc
    ((formula.clauses.zipIdx.map fun tagged =>
        portSegmentExtrasForDegree
          (portsAt graph (.clause tagged.2)).length).sum) =
      (formula.clauses.zipIdx.map fun tagged =>
        portSegmentExtrasForDegree tagged.1.length).sum := by
      congr 1
      apply List.map_congr_left
      intro tagged taggedMember
      rw [portsAt_length,
        PeriodicCNF.incidenceGraph_clause_degree_eq_of_tagged
          formula tagged taggedMember]
    _ = (formula.clauses.map fun clause =>
          portSegmentExtrasForDegree clause.length).sum := by
      rw [show formula.clauses.zipIdx.map (fun tagged =>
          portSegmentExtrasForDegree tagged.1.length) =
        (formula.clauses.zipIdx.map Prod.fst).map (fun clause =>
          portSegmentExtrasForDegree clause.length) by
            rw [List.map_map]
            rfl]
      rw [List.zipIdx_map_fst]

end PeriodicOrthocrossing
end LeanTrominoes

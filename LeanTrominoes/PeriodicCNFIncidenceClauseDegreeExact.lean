/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraph

/-! # Exact clause degrees in the periodic CNF incidence graph -/

namespace LeanTrominoes
namespace PeriodicCNF

theorem clauseWeight_sum_eq_of_mem
    {Variable : Type*}
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (tagged : PeriodicClause Variable × Nat)
    (indicesNodup : (taggedClauses.map Prod.snd).Nodup)
    (taggedMember : tagged ∈ taggedClauses) :
    (taggedClauses.map fun item =>
      if item.2 = tagged.2 then item.1.length else 0).sum =
        tagged.1.length := by
  induction taggedClauses with
  | nil => simp at taggedMember
  | cons head rest induction =>
      have headNotMember : head.2 ∉ rest.map Prod.snd :=
        (List.nodup_cons.mp indicesNodup).1
      have restNodup : (rest.map Prod.snd).Nodup :=
        (List.nodup_cons.mp indicesNodup).2
      simp only [List.mem_cons] at taggedMember
      rcases taggedMember with rfl | taggedMember
      · simp only [List.map_cons, List.sum_cons, if_pos]
        rw [clauseWeight_sum_eq_zero_of_not_mem
          rest tagged.2 headNotMember, Nat.add_zero]
      · have headNe : head.2 ≠ tagged.2 := by
          intro equal
          apply headNotMember
          exact List.mem_map.mpr ⟨tagged, taggedMember, equal.symm⟩
        simp only [List.map_cons, List.sum_cons, if_neg headNe,
          Nat.zero_add]
        exact induction restNodup taggedMember

/-- A genuine indexed clause vertex has degree exactly its clause length. -/
theorem incidenceGraph_clause_degree_eq_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : PeriodicClause Variable × Nat)
    (taggedMember : tagged ∈ formula.clauses.zipIdx) :
    (incidenceGraph formula).incidences.count
        (.clause tagged.2) = tagged.1.length := by
  rw [show (incidenceGraph formula).incidences =
    (formula.clauses.zipIdx.flatMap fun item =>
      clauseIncidenceEdges item.2 item.1).flatMap
        PeriodicEdge.incidences by rfl]
  rw [taggedIncidenceEdges_clause_count]
  exact clauseWeight_sum_eq_of_mem
    formula.clauses.zipIdx tagged
    (List.nodup_zipIdx_map_snd formula.clauses) taggedMember

end PeriodicCNF
end LeanTrominoes

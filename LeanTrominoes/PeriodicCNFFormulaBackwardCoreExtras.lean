/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseBackwardCoreExtras

/-! # Formula-wide backward-core extras -/

namespace LeanTrominoes
namespace PeriodicCNF

open UnaryProgramClauseProfile

theorem taggedClauseIncidenceEdges_backwardCoreExtra_sum
    {Variable : Type}
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (forward : ∀ tagged ∈ taggedClauses,
      ∀ literal ∈ tagged.1, literal.IsForwardLocal) :
    ((taggedClauses.flatMap fun tagged =>
        clauseIncidenceEdges tagged.2 tagged.1).map fun edge =>
          PeriodicOrthocrossing.backwardCoreSegmentExtra edge.offset).sum =
      (taggedClauses.map fun tagged =>
        literalProfilesBackwardCoreExtras
          (ClauseProfileOccurrenceSplit.literalProfiles tagged.1)).sum := by
  induction taggedClauses with
  | nil => rfl
  | cons tagged taggedClauses induction =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [clauseIncidenceEdges_backwardCoreExtra_sum
        tagged.2 tagged.1 (forward tagged (by simp))]
      rw [induction (fun later laterMember =>
        forward later (by simp [laterMember]))]

/-- The complete incidence-edge presentation has exactly the backward-core
weight read from each finite clause profile. -/
theorem incidenceGraph_backwardCoreExtra_sum
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal) :
    ((incidenceGraph formula).edges.map fun edge =>
      PeriodicOrthocrossing.backwardCoreSegmentExtra edge.offset).sum =
      (formula.clauses.map fun clause =>
        literalProfilesBackwardCoreExtras
          (ClauseProfileOccurrenceSplit.literalProfiles clause)).sum := by
  unfold incidenceGraph
  have taggedForward :
      ∀ tagged ∈ formula.clauses.zipIdx,
        ∀ literal ∈ tagged.1, literal.IsForwardLocal := by
    intro tagged taggedMember literal literalMember
    exact forward tagged.1
      (List.fst_mem_of_mem_zipIdx taggedMember)
      literal literalMember
  have total := taggedClauseIncidenceEdges_backwardCoreExtra_sum
    formula.clauses.zipIdx taggedForward
  rw [show formula.clauses.map (fun clause =>
      literalProfilesBackwardCoreExtras
        (ClauseProfileOccurrenceSplit.literalProfiles clause)) =
    formula.clauses.zipIdx.map (fun tagged =>
      literalProfilesBackwardCoreExtras
        (ClauseProfileOccurrenceSplit.literalProfiles tagged.1)) by
      rw [show formula.clauses.zipIdx.map (fun tagged =>
          literalProfilesBackwardCoreExtras
            (ClauseProfileOccurrenceSplit.literalProfiles tagged.1)) =
        (formula.clauses.zipIdx.map Prod.fst).map (fun clause =>
          literalProfilesBackwardCoreExtras
            (ClauseProfileOccurrenceSplit.literalProfiles clause)) by
            rw [List.map_map]
            rfl,
        List.zipIdx_map_fst]]
  exact total

end PeriodicCNF
end LeanTrominoes

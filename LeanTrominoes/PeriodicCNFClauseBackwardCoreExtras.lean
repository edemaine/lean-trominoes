/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicCNFTransition
import LeanTrominoes.PeriodicOrthocrossingHorizontalRouteSegmentCount

/-! # Backward-core extras from finite clause profiles -/

namespace LeanTrominoes
namespace PeriodicCNF

open UnaryProgramClauseProfile

/-- Two extra core segments are needed exactly when a next-slice clause
anchor routes back to a current-slice literal. -/
def literalBackwardCoreExtra
    (first literal : LiteralProfile) : Nat :=
  if first.nextSlice && !literal.nextSlice then 2 else 0

def literalProfilesBackwardCoreExtras : List LiteralProfile -> Nat
  | [] => 0
  | first :: rest =>
      ((first :: rest).map (literalBackwardCoreExtra first)).sum

def ClauseProfile.backwardCoreExtras (profile : ClauseProfile) : Nat :=
  literalProfilesBackwardCoreExtras profile.literals

@[simp] theorem literalProfilesBackwardCoreExtras_nil :
    literalProfilesBackwardCoreExtras [] = 0 := rfl

@[simp] theorem literalProfilesBackwardCoreExtras_cons
    (first : LiteralProfile) (rest : List LiteralProfile) :
    literalProfilesBackwardCoreExtras (first :: rest) =
      ((first :: rest).map (literalBackwardCoreExtra first)).sum := rfl

theorem backwardCoreSegmentExtra_incidenceEdge_eq_profile
    {Variable : Type} (clauseIndex : Nat)
    (first literal : PeriodicLiteral Variable)
    (firstForward : first.IsForwardLocal)
    (literalForward : literal.IsForwardLocal) :
    PeriodicOrthocrossing.backwardCoreSegmentExtra
        (incidenceEdge clauseIndex first.offset literal).offset =
      literalBackwardCoreExtra
        { nextSlice := decide (first.offset = (1, 0)),
          value := first.value }
        { nextSlice := decide (literal.offset = (1, 0)),
          value := literal.value } := by
  rcases firstForward with firstCurrent | firstNext <;>
    rcases literalForward with literalCurrent | literalNext
  all_goals simp_all [incidenceEdge, Cell.sub,
    PeriodicOrthocrossing.backwardCoreSegmentExtra,
    literalBackwardCoreExtra]

/-- Summing geometric backward-core extras over a clause's incidence edges
is exactly the finite literal-profile weight. -/
theorem clauseIncidenceEdges_backwardCoreExtra_sum
    {Variable : Type} (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (forward : ∀ literal ∈ clause, literal.IsForwardLocal) :
    ((clauseIncidenceEdges clauseIndex clause).map fun edge =>
      PeriodicOrthocrossing.backwardCoreSegmentExtra edge.offset).sum =
      literalProfilesBackwardCoreExtras
        (ClauseProfileOccurrenceSplit.literalProfiles clause) := by
  cases clause with
  | nil => rfl
  | cons first rest =>
      unfold clauseIncidenceEdges clauseAnchor
        ClauseProfileOccurrenceSplit.literalProfiles
      simp only [List.head?_cons, Option.map_some, Option.getD_some,
        List.map_cons, literalProfilesBackwardCoreExtras_cons]
      congr 1
      congr 1
      · exact backwardCoreSegmentExtra_incidenceEdge_eq_profile
          clauseIndex first first
            (forward first (by simp))
            (forward first (by simp))
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro literal literalMember
      exact backwardCoreSegmentExtra_incidenceEdge_eq_profile
          clauseIndex first literal
          (forward first (by simp))
          (forward literal (by simp [literalMember]))

end PeriodicCNF
end LeanTrominoes

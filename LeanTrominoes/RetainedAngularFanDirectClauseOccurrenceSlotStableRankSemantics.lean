/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRankSemantics

/-! # Stable-rank semantics of direct-clause occurrence slots -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PeriodicEightOccurrenceSplitPositioned

set_option maxHeartbeats 300000

/-- A genuine final copied clause's semantic Figure 7 slot tuple is obtained
by bounding each literal occurrence's stable numeric terminal rank, in the
original clause presentation order. -/
theorem retainedFinalDirectClauseOccurrenceSlots_eq_stableTerminalRanks
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula))
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx) :
    retainedFinalDirectClauseOccurrenceSlots formula clauseIndex clause =
      RetainedDirectClauseOccurrenceSlots.ofList
        (clause.literals.zipIdx.map fun taggedLiteral =>
          boundedRetainedTerminalSlot
            (retainedFinalCoordinatedOccurrenceStableTerminalRank
              formula taggedLiteral.1 clauseIndex taggedLiteral.2)) := by
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        (retainedFinalCoordinatedScaledSource formula).clauses.zipIdx := by
    unfold retainedFinalCoordinatedScaledSource
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  unfold retainedFinalDirectClauseOccurrenceSlots
  apply congrArg RetainedDirectClauseOccurrenceSlots.ofList
  apply List.map_congr_left
  intro taggedLiteral literalMember
  have taggedMember :=
    taggedLiteral_mem_of_positioned_members
      (retainedFinalCoordinatedScaledSource formula)
      scaledClauseMember literalMember
  exact
    retainedFinalCoordinatedOccurrenceSlot_eq_boundedStableTerminalRank
      formula taggedLiteral.1 clauseIndex taggedLiteral.2 certificate
      taggedMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes

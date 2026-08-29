/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseOccurrenceSlotGlobalStableRankSemantics

/-! # Attaching global stable-rank slots to direct clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Attaching a genuine clause's packed global stable-rank block to its
exact indexed direction query recovers the full semantic route-tail query. -/
theorem retainedDirectClauseRouteTailRecordQueryOfGlobalStableRankBlock
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (position : Cell)
    (taggedClause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula))
    (clauseMember : taggedClause ∈
      (retainedFinalCoordinatedScaledSource formula).erase.clauses.zipIdx)
    (clauseNonempty : taggedClause.1 ≠ [])
    (clauseWidth : taggedClause.1.length ≤ 3)
    (choicesSome : ∀ taggedLiteral ∈ taggedClause.1.zipIdx,
      ∃ choice,
        retainedFinalDirectSourceRouteChoice?
            formula taggedClause.2 taggedLiteral.2 = some choice) :
    retainedDirectClauseRouteTailRecordQueryOfSlotInput
        (retainedFinalCopiedClauseQueryOfLiterals
            formula taggedClause.2 taggedClause.1,
          RetainedDirectClauseOccurrenceSlots.ofList
            (retainedOccurrenceGlobalStableTerminalSlotBlock
              (retainedFinalCoordinatedScaledSource formula).erase
              (retainedFinalCoordinatedScaledSourceRoutes formula)
              taggedClause)) =
      some (retainedFinalDirectClauseRouteTailRecordQuery
        formula taggedClause.2 ⟨position, taggedClause.1⟩) := by
  rw [show
    (retainedFinalCopiedClauseQueryOfLiterals
        formula taggedClause.2 taggedClause.1,
      RetainedDirectClauseOccurrenceSlots.ofList
        (retainedOccurrenceGlobalStableTerminalSlotBlock
          (retainedFinalCoordinatedScaledSource formula).erase
          (retainedFinalCoordinatedScaledSourceRoutes formula)
          taggedClause)) =
      retainedFinalDirectClauseRouteTailRecordSlotInput
        formula taggedClause.2 ⟨position, taggedClause.1⟩ by
    apply Prod.ext
    · rfl
    · exact
        (retainedFinalDirectClauseOccurrenceSlots_eq_globalStableRankBlock
          formula position taggedClause certificate clauseMember).symm]
  exact retainedDirectClauseRouteTailRecordQueryOfSlotInput_semantic
    formula taggedClause.2 ⟨position, taggedClause.1⟩
    clauseNonempty clauseWidth choicesSome

end PeriodicEightOccurrenceSplit
end LeanTrominoes

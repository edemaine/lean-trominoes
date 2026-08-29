/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotPairSemantics
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperSemantics

/-! # Semantics of final copied-clause slot inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotInputSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotInputSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled slot inputs are exactly the five-family final query stream
grouped against the presentation-ordered bounded stable-rank stream. -/
theorem directSourceFinalClauseRouteTailRecordSlotInputs_eq_grouped
    (symbols : List encoding.Γ) :
    directSourceFinalClauseRouteTailRecordSlotInputs decider symbols =
      FinalOccurrenceRoleSlotGrouper.slotInputsOfQueries
        (directRetainedFinalClauseQueryAssembly decider symbols)
        (BoundedRetainedTerminalSlots.slots
          (retainedOccurrenceGlobalStableTerminalRanks
            (retainedFinalCoordinatedScaledSource
              (directSourceFormula decider symbols)).erase
            (retainedFinalCoordinatedScaledSourceRoutes
              (directSourceFormula decider symbols)))) := by
  have lengthEq :=
    directSourceFinalOccurrenceRoleBaseValues_length_eq_slots
      decider symbols
  unfold directSourceFinalOccurrenceRoleBaseValues
    directSourceFinalTerminalSlotValues FiniteUnaryFieldMap.values at lengthEq
  simp only [List.length_map] at lengthEq
  unfold directSourceFinalClauseRouteTailRecordSlotInputs
  rw [directSourceFinalOccurrenceRoleSlotPairs_eq_zip decider symbols]
  exact FinalOccurrenceRoleSlotGrouper.slotInputs_zip_occurrenceRoles
    _ _ lengthEq

end LeanTrominoes.PeriodicCNFStripReduction

end

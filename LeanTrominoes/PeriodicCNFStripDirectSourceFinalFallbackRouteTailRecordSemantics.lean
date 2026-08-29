/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachmentListSemantics

/-! # Rejection of fallback final route-tail queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackRouteTailStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The adjacent carrier and bend wrapper queries produce no direct
route-tail records for any aligned slot tuple list. -/
theorem directSourceFinalFallbackRouteTailRecordQueries_nil
    (symbols : List encoding.Γ)
    (slots : List RetainedDirectClauseOccurrenceSlots) :
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
        (List.zip
          (directRetainedFinalCarrierClauseQueries decider symbols ++
            directRetainedFinalBendClauseQueries decider symbols)
          slots) = [] := by
  unfold directRetainedFinalCarrierClauseQueries
    directRetainedFinalBendClauseQueries
  rw [← retainedFinalPrecomputedClauseQueries_append]
  exact
    retainedDirectClauseRouteTailRecordQueriesOfSlotInputs_zip_precomputed
      _ _

end LeanTrominoes.PeriodicCNFStripReduction

end

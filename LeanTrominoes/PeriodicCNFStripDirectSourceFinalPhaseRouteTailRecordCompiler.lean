/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotInputCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPhaseRouteTailRecordData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilterCompiler
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachmentCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compilers for phase-split final direct-clause route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalPhaseRouteTailRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The complete slot compiler followed by the crossover selector. -/
noncomputable def
    directSourceFinalCrossoverRouteTailRecordSlotInputsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List RetainedDirectClauseRouteTailRecordSlotInput)
      encoding.Γ RetainedDirectClauseRouteTailRecordSlotInput
      id id
      (directSourceFinalCrossoverRouteTailRecordSlotInputs decider) := by
  unfold directSourceFinalCrossoverRouteTailRecordSlotInputs
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseRouteTailRecordSlotInputsComputableInPolyTime
      decider)
    retainedDirectCrossoverRouteTailRecordSlotInputsComputableInPolyTime

/-- The complete slot compiler followed by the routed-family selector. -/
noncomputable def
    directSourceFinalRoutedRouteTailRecordSlotInputsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List RetainedDirectClauseRouteTailRecordSlotInput)
      encoding.Γ RetainedDirectClauseRouteTailRecordSlotInput
      id id
      (directSourceFinalRoutedRouteTailRecordSlotInputs decider) := by
  unfold directSourceFinalRoutedRouteTailRecordSlotInputs
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseRouteTailRecordSlotInputsComputableInPolyTime
      decider)
    retainedDirectRoutedRouteTailRecordSlotInputsComputableInPolyTime

/-- Exact direct crossover route-tail records compile in polynomial time. -/
noncomputable def
    directSourceFinalCrossoverRouteTailRecordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List HorizontalRoutedRouteTailRecord.Token)
      encoding.Γ HorizontalRoutedRouteTailRecord.Token
      id id
      (directSourceFinalCrossoverRouteTailRecordTokens decider) := by
  unfold directSourceFinalCrossoverRouteTailRecordTokens
  exact retainedDirectClauseRouteTailRecordTokensComputableInPolyTimeOf
    id
    (directSourceFinalCrossoverRouteTailRecordSlotInputs decider)
    (directSourceFinalCrossoverRouteTailRecordSlotInputsComputableInPolyTime
      decider)

/-- Exact direct routed route-tail records compile in polynomial time. -/
noncomputable def
    directSourceFinalRoutedRouteTailRecordTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List HorizontalRoutedRouteTailRecord.Token)
      encoding.Γ HorizontalRoutedRouteTailRecord.Token
      id id
      (directSourceFinalRoutedRouteTailRecordTokens decider) := by
  unfold directSourceFinalRoutedRouteTailRecordTokens
  exact retainedDirectClauseRouteTailRecordTokensComputableInPolyTimeOf
    id
    (directSourceFinalRoutedRouteTailRecordSlotInputs decider)
    (directSourceFinalRoutedRouteTailRecordSlotInputsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

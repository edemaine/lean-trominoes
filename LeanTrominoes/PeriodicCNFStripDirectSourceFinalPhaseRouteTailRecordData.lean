/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteTailRecordData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter

/-! # Phase-split final direct-clause Figure 9 route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalPhaseRouteTailRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Slot inputs for the crossover prefix of the copied-clause record phase. -/
def directSourceFinalCrossoverRouteTailRecordSlotInputs
    (symbols : List encoding.Γ) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  retainedDirectCrossoverRouteTailRecordSlotInputs
    (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols)

/-- Slot inputs for both routed suffix families of the copied-clause record
phase. -/
def directSourceFinalRoutedRouteTailRecordSlotInputs
    (symbols : List encoding.Γ) :
    List RetainedDirectClauseRouteTailRecordSlotInput :=
  retainedDirectRoutedRouteTailRecordSlotInputs
    (directSourceFinalClauseRouteTailRecordSlotInputs decider symbols)

/-- Exact route-tail record word for the direct crossover prefix. -/
def directSourceFinalCrossoverRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  retainedDirectClauseRouteTailRecordStream
    (retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
      (directSourceFinalCrossoverRouteTailRecordSlotInputs decider symbols))

/-- Exact route-tail record word for the two routed direct suffix families. -/
def directSourceFinalRoutedRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  retainedDirectClauseRouteTailRecordStream
    (retainedDirectClauseRouteTailRecordQueriesOfSlotInputs
      (directSourceFinalRoutedRouteTailRecordSlotInputs decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end

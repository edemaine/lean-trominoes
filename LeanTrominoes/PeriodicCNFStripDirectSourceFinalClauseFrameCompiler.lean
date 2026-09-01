/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseFrameData
import LeanTrominoes.TM2CompositionMachine

/-! # Direct final clause-local occurrence frames -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseFrameStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Clause fan, terminal group, and original finite header aligned with every
final routed occurrence. -/
def directSourceFinalClauseFrames
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderClauseFrame.Data :=
  HorizontalRoutedRouteHeaderClauseFrame.output
    (directSourceFinalClauseDescriptors decider symbols)

/-- The complete clause-local frame column is polynomial-time computable. -/
noncomputable def directSourceFinalClauseFramesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseFrames decider) := by
  unfold directSourceFinalClauseFrames
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderClauseFrame.computableInPolyTime

/-- Projecting occurrence data from the retained headers recovers the exact
compiled final occurrence stream. -/
theorem directSourceFinalClauseFrames_map_occurrenceData
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrames decider symbols).map
        (HorizontalRoutedRouteHeader.occurrenceData ∘
          HorizontalRoutedRouteHeaderClauseFrame.Data.header) =
      directSourceFinalCompiledOccurrenceData decider symbols := by
  unfold directSourceFinalClauseFrames
  rw [HorizontalRoutedRouteHeaderClauseFrame.output_map_occurrenceData]
  exact directSourceFinalClauseDescriptors_occurrenceData_eq
    decider symbols

/-- There is exactly one clause-local frame per compiled final occurrence. -/
@[simp] theorem directSourceFinalClauseFrames_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrames decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  have aligned := congrArg List.length
    (directSourceFinalClauseFrames_map_occurrenceData decider symbols)
  simpa using aligned

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceEndpointFrameData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct final colored occurrence-endpoint frame compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceEndpointFrameStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Three finite endpoint frames per final routed occurrence, in canonical
incidence-color order. -/
def directSourceFinalOccurrenceEndpointFrames
    (symbols : List encoding.Γ) :
    List DirectFinalOccurrenceEndpointFrame.Data :=
  DirectFinalOccurrenceEndpointFrame.output
    (directSourceFinalOccurrenceFrames decider symbols)

@[simp] theorem directSourceFinalOccurrenceEndpointFrames_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceEndpointFrames decider symbols).length =
      3 * (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceEndpointFrames
  rw [DirectFinalOccurrenceEndpointFrame.output_length,
    directSourceFinalOccurrenceFrames_length]

/-- The complete colored endpoint-frame stream is polynomial-time computable
from the direct source symbols. -/
noncomputable def
    directSourceFinalOccurrenceEndpointFramesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalOccurrenceEndpointFrames decider) := by
  unfold directSourceFinalOccurrenceEndpointFrames
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceFramesComputableInPolyTime decider)
    DirectFinalOccurrenceEndpointFrame.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

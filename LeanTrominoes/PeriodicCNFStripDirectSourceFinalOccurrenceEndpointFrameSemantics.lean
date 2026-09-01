/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceEndpointFrameCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameSemantics

/-! # Semantics of direct final colored occurrence-endpoint frames -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Declarative endpoint-frame expansion of the exact three-column occurrence
frame assembly. -/
def directSourceFinalOccurrenceEndpointFramesExpected
    (symbols : List encoding.Γ) :
    List DirectFinalOccurrenceEndpointFrame.Data :=
  DirectFinalOccurrenceEndpointFrame.output
    (directSourceFinalOccurrenceFramesExpected decider symbols)

/-- The endpoint-frame compiler expands exactly the declaratively assembled
complete occurrence frames. -/
theorem directSourceFinalOccurrenceEndpointFrames_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceEndpointFrames decider symbols =
      directSourceFinalOccurrenceEndpointFramesExpected decider symbols := by
  unfold directSourceFinalOccurrenceEndpointFrames
    directSourceFinalOccurrenceEndpointFramesExpected
  rw [directSourceFinalOccurrenceFrames_eq_expected]

end LeanTrominoes.PeriodicCNFStripReduction

end

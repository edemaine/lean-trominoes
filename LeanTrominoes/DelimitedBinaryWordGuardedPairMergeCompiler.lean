/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData
import LeanTrominoes.FiniteStateTransducerFunctionSemantics
import LeanTrominoes.FiniteStateTransducerTime

/-! # Polynomial-time guarded word-pair merger -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open Computability Turing

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens := by
  have outputEqual :
      (LightweightFiniteStateTransducer.output
        Control.firstStart transition finish) =
      (FiniteStateTransducer.output
        Control.firstStart transition finish) := by
    funext source
    exact LightweightFiniteStateTransducer.output_eq_finiteState
      Control.firstStart transition finish source
  unfold tokens
  rw [outputEqual]
  exact FiniteStateTransducer.computableInPolyTime
    Control.firstStart transition finish

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

end

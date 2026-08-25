/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorData
import LeanTrominoes.FiniteStateTransducerTime

/-! # Polynomial-time adjacent binary-word pair selection -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordPairSelector

open Computability Turing

noncomputable def tokensComputableInPolyTime (side : Side) :
    TM2ComputableInPolyTime id id (tokens side) := by
  unfold tokens
  exact FiniteStateTransducer.computableInPolyTime
    Control.first (transition side) finish

end LeanTrominoes.DelimitedBinaryWordPairSelector

end

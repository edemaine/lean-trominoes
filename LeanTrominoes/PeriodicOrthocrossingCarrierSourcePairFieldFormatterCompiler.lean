/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterData

/-! # Compiler for guarded source-pair words from unary fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourcePairFieldFormatter

open Computability Turing

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  unfold output
  exact FiniteStateTransducer.computableInPolyTime
    Control.begin transition finish

end CarrierSourcePairFieldFormatter
end LeanTrominoes.PeriodicOrthocrossing

end

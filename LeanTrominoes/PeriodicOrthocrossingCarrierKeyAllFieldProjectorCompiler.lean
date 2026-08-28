/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorData

/-! # Compiler for all guarded carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAllFieldProjector

open Computability Turing

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  unfold output
  exact FiniteStateTransducer.computableInPolyTime
    Control.outside transition finish

end CarrierKeyAllFieldProjector
end LeanTrominoes.PeriodicOrthocrossing

end

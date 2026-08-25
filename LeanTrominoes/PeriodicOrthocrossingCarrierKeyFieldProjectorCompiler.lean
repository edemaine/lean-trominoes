/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData

/-! # Compiler for all guarded carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

open Computability Turing

/-- Every fixed carrier-key column is projected in polynomial time. -/
noncomputable def computableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (output field) := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output Control.outside
      (transition field) finish)
  exact FiniteStateTransducer.computableInPolyTime
    Control.outside (transition field) finish

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing

end

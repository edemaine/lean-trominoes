/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData

/-! # Compiler for constant guarded presence fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedPresenceFieldProjector

open Computability Turing

noncomputable def computableInPolyTime (activeValue : Bool) :
    TM2ComputableInPolyTime id id (output activeValue) := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output Control.outside
      (transition activeValue) finish)
  exact FiniteStateTransducer.computableInPolyTime
    Control.outside (transition activeValue) finish

end GuardedPresenceFieldProjector
end LeanTrominoes.PeriodicOrthocrossing

end

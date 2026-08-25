/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorData

/-! # Compiler for guarded carrier-key route fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRouteFieldProjector

open Computability Turing

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output Control.outside transition finish)
  exact FiniteStateTransducer.computableInPolyTime
    Control.outside transition finish

end CarrierKeyRouteFieldProjector
end LeanTrominoes.PeriodicOrthocrossing

end

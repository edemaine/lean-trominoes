/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordSemantics

/-! # Compiler for route-descriptor target atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorTargetAtomWords

open Computability Turing

/-- The fixed target-field projector runs in polynomial time. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteStateTransducer.computableInPolyTime 0 transition finish

end RouteDescriptorTargetAtomWords
end PeriodicOrthocrossing
end LeanTrominoes

end

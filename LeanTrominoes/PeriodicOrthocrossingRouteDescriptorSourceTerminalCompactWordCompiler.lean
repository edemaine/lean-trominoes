/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordSemantics

/-! # Compiler for route-descriptor source-terminal compact words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorSourceTerminalCompactWords

open Computability Turing

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteStateTransducer.computableInPolyTime 0 transition finish

end RouteDescriptorSourceTerminalCompactWords
end PeriodicOrthocrossing
end LeanTrominoes

end

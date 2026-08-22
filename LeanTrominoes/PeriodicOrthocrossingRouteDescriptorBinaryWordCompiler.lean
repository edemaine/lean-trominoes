/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData

/-! # Fixed compiler from route-descriptor records to binary words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWords

open Computability Turing

/-- Encoding normalized descriptor records as binary words is a fixed
finite-state transduction. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteStateTransducer.computableInPolyTime 0 transition finish

end RouteDescriptorBinaryWords
end PeriodicOrthocrossing
end LeanTrominoes

end

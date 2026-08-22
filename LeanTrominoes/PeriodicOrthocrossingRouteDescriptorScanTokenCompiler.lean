/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenSemantics

/-! # Fixed compiler for normalized route-descriptor scan tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorScanTokens

open Computability Turing

/-- Normalizing unary-program tokens is a fixed finite block transduction. -/
noncomputable def normalizeComputableInPolyTime :
    TM2ComputableInPolyTime id id normalize :=
  FiniteBlockTransducer.computableInPolyTime normalizeBlock

end RouteDescriptorScanTokens
end PeriodicOrthocrossing
end LeanTrominoes

end

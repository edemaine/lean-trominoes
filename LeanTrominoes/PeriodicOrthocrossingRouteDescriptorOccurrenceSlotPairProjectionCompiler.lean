/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTags

/-! # Compiler for descriptor projection from occurrence-slot pair tags -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

open Computability Turing

/-- Deleting the twelfth slot field while preserving descriptor tags is a
fixed finite block substitution. -/
noncomputable def descriptorTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id descriptorTokens := by
  change TM2ComputableInPolyTime id id
    (fun source => source.flatMap descriptorProjection)
  exact FiniteBlockTransducer.computableInPolyTime descriptorProjection

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing

end

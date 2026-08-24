/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCandidateSupport

/-! # Activity support of the compact source-key candidate stream -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

theorem paddedCarrierSourceKeyCandidateStream_supported_eq_isSome
    (descriptors : List RouteDescriptor) :
    ∀ candidate ∈ paddedCarrierSourceKeyCandidateStream descriptors,
      candidate.supported = candidate.value.isSome := by
  intro candidate member
  rcases List.mem_map.mp member with ⟨node, _nodeMember, rfl⟩
  exact sourceKeyCandidate_supported_eq_isSome node

end LeanTrominoes.PeriodicOrthocrossing

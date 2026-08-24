/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCandidateStreamMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCodeSelectionSemantics

/-! # Compact source-key and carrier-identity selection -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Once the padded node stream compacts to the retained nodes, its compact
source-key rows select exactly the same slots as its full identity rows. -/
theorem selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_of_filterMap
    (period : Nat) (descriptors : List RouteDescriptor)
    (activeValues :
      (paddedCarrierNodeCandidateStream descriptors).filterMap
          Candidate.value =
        routeDescriptorRetainedCarrierNodesAtPeriod period descriptors) :
    selectedRows (paddedCarrierSourceKeyCandidateStream descriptors) =
      selectedRows
        (paddedCarrierIdentityCandidateStreamAtPeriod period descriptors) := by
  rw [paddedCarrierSourceKeyCandidateStream_eq_mapActiveValue,
    paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue]
  exact
    selectedRows_sourceKey_eq_code_of_filterMap_eq_retainedCarrierNodes
      period descriptors (paddedCarrierNodeCandidateStream descriptors)
      activeValues

end LeanTrominoes.PeriodicOrthocrossing

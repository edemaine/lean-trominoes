/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMapSelection
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCodeEqualitySemantics

/-! # Compact source-key and carrier-code representative selection -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Any padded stream whose active values are exactly the retained carrier
nodes has identical compact-source-key and reversible-code representative
selection. -/
theorem selectedRows_sourceKey_eq_code_of_filterMap_eq_retainedCarrierNodes
    (period : Nat) (descriptors : List RouteDescriptor)
    (candidates : List (Candidate CarrierNode))
    (activeValues : candidates.filterMap Candidate.value =
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors) :
    selectedRows
        (candidates.map
          (Candidate.mapActiveValue CarrierNodeSourceKeys.pair)) =
      selectedRows
        (candidates.map (Candidate.mapActiveValue CarrierNode.code)) := by
  apply selectedRows_mapActiveValue_eq_of_eq_iff_on_filterMap
    CarrierNodeSourceKeys.pair CarrierNode.code candidates
  intro first firstMember second secondMember
  apply sourceKeyPair_eq_iff_code_eq_of_mem_retainedCarrierNodes
    period descriptors first second
  · rw [← activeValues]
    exact firstMember
  · rw [← activeValues]
    exact secondMember

end LeanTrominoes.PeriodicOrthocrossing

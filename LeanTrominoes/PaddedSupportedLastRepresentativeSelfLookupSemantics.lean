/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListOptionSupportedDedup
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSentinelSemantics

/-! # Unary lookups from self-supported padded candidates -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- If support is exactly activity, selected rows look up an arbitrary datum
once for each distinct active value, in stable last-occurrence order. -/
theorem lookups_selectedRows_selfSupported_map_append_value
    (candidates : List (Candidate Value))
    (supportEq : ∀ candidate ∈ candidates,
      candidate.supported = candidate.value.isSome)
    (datum : Option Value → Nat) (sentinel : Nat) :
    LastTrueUnaryValueLookupMachine.lookups
        (selectedRows candidates).words
        ((values candidates).map datum ++ [sentinel]) =
      (candidates.filterMap Candidate.value).dedup.map fun value =>
        datum (some value) := by
  let active := candidates.filterMap Candidate.value
  have correct : CorrectSupport active candidates :=
    correctSupport_filterMap_of_supported_eq_isSome candidates supportEq
  rw [lookups_selectedRows_map_append_value
    active candidates correct datum sentinel]
  rw [List.dedup_filter_mem_map_some_eq]
  have valuesFilterMap : (values candidates).filterMap id = active := by
    unfold active values
    rw [List.filterMap_map]
    rfl
  rw [valuesFilterMap]
  have retainAll :
      active.dedup.filter (fun value => decide (value ∈ active)) =
        active.dedup := by
    apply List.filter_eq_self.mpr
    intro value valueMember
    simp only [decide_eq_true_eq]
    exact List.mem_dedup.mp valueMember
  rw [retainAll, List.map_map]
  rfl

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

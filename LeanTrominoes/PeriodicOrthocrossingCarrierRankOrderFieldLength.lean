/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeSelfLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateNodeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeRowSemantics

/-! # Alignment of selected carrier-key and order-coordinate fields -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

theorem selectedRows_length_eq_activeDedup
    {Value : Type*} [DecidableEq Value]
    (candidates : List (Candidate Value))
    (supportEq : ∀ candidate ∈ candidates,
      candidate.supported = candidate.value.isSome) :
    (selectedRows candidates).words.length =
      (candidates.filterMap Candidate.value).dedup.length := by
  have lookupEq :=
    lookups_selectedRows_selfSupported_map_append_value
      candidates supportEq (fun _ => 0) 0
  have lengths := congrArg List.length lookupEq
  simpa [LastTrueUnaryValueLookupMachine.lookups] using lengths

theorem sourceKeyCandidates_selfSupported
    (candidates : List (Candidate CarrierNode)) :
    ∀ candidate ∈ candidates.map
        CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate,
      candidate.supported = candidate.value.isSome := by
  intro candidate candidateMember
  rcases List.mem_map.mp candidateMember with
    ⟨source, _sourceMember, rfl⟩
  rcases source with ⟨value, supported⟩
  cases value <;>
    rfl

theorem filterMap_sourceKeyCandidates
    (candidates : List (Candidate CarrierNode)) :
    (candidates.map
        CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate).filterMap
        Candidate.value =
      (candidates.filterMap Candidate.value).map
        CarrierNodeSourceKeys.pair := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;>
        simp [CarrierNodeSourceKeyCandidateWords.sourceKeyCandidate,
          induction]

/-- The two independently compiled representative-row pipelines select the
same number of distinct active source identities on every descriptor input. -/
theorem orderRepresentativeRows_length_eq_sourceKeyRepresentativeRows
    (descriptors : List RouteDescriptor) :
    (CarrierOrderRepresentativeRows.rows descriptors).words.length =
      (paddedCarrierSourceKeyRepresentativeRows descriptors).words.length := by
  rw [CarrierOrderRepresentativeRows.rows_eq_selectedRows_carrierOrderCandidateNodeStream,
    paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows]
  unfold paddedCarrierSourceKeyCandidateStream
  rw [selectedRows_length_eq_activeDedup
      _ (sourceKeyCandidates_selfSupported _),
    selectedRows_length_eq_activeDedup
      _ (sourceKeyCandidates_selfSupported _),
    filterMap_sourceKeyCandidates,
    filterMap_sourceKeyCandidates,
    filterMap_carrierOrderCandidateNodeStream]

namespace CarrierRankOrderField

/-- Either selected order-coordinate polarity has one value per selected
carrier-key datum, unconditionally on the descriptor stream. -/
theorem values_length_eq_keyValues
    (keepPositive : Bool) (field : CarrierKeyFieldProjector.Field)
    (descriptors : List RouteDescriptor) :
    (values keepPositive descriptors).length =
      (CarrierRankKeyField.values field descriptors).length := by
  unfold values CarrierOrderRepresentativeLookup.values
    CarrierRankKeyField.values CarrierSourceKeyRepresentativeLookup.values
    LastTrueUnaryValueLookupMachine.lookups
  simp only [List.length_map]
  exact orderRepresentativeRows_length_eq_sourceKeyRepresentativeRows
    descriptors

end CarrierRankOrderField
end LeanTrominoes.PeriodicOrthocrossing

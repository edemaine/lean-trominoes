/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanKindSemantics

/-! # Route-field alignment of grouped final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreeToThreeDM
open PeriodicPlanarOneInThreeToThreeDM

private theorem forall₂_map_same
    {Key First Second : Type*} (relation : First → Second → Prop)
    (first : Key → First) (second : Key → Second) (keys : List Key)
    (property : ∀ key ∈ keys, relation (first key) (second key)) :
    List.Forall₂ relation (keys.map first) (keys.map second) := by
  induction keys with
  | nil => exact .nil
  | cons key keys induction =>
      exact .cons (property key (by simp))
        (induction fun other otherMember =>
          property other (by simp [otherMember]))

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every grouped fan/slot selects the polarity stored in its aligned finite
occurrence record. -/
theorem directSourceFinalGroupedVariableFanSlotPolarities
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun pair data =>
        pair.1.polarity (groupedVariableFanSiteSlot pair.2) = data.polarity)
      (directSourceFinalGroupedVariableFanSlots decider symbols)
      (directSourceFinalGroupedOccurrenceData decider symbols) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_map_stableFan,
    directSourceFinalGroupedOccurrenceData_eq_map_alignedDatum]
  apply forall₂_map_same
  intro key keyMember
  have candidateMember : key ∈
      directSourceFinalOccurrenceCandidateKeys decider symbols :=
    directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols key keyMember
  have candidateMember' : key ∈ StableOccurrenceRanks.candidateKeys
      (directSourceFinalAtomIdentityCodes decider symbols) := by
    rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    exact candidateMember
  simp only [groupedVariableFanSiteSlot_genericSlot]
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  exact FinalFanDataTripleAssembler.stableFan_polarity_of_candidateKey
    (directSourceFinalAtomIdentityCodes decider symbols)
    (directSourceFinalVariableOccurrenceData decider symbols)
    (fun value _valueMember =>
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value)
    key candidateMember'

/-- Every grouped fan/slot selects the direction stored in its aligned finite
occurrence record. -/
theorem directSourceFinalGroupedVariableFanSlotDirections
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun pair data =>
        pair.1.direction (groupedVariableFanSiteSlot pair.2) = data.direction)
      (directSourceFinalGroupedVariableFanSlots decider symbols)
      (directSourceFinalGroupedOccurrenceData decider symbols) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_map_stableFan,
    directSourceFinalGroupedOccurrenceData_eq_map_alignedDatum]
  apply forall₂_map_same
  intro key keyMember
  have candidateMember : key ∈
      directSourceFinalOccurrenceCandidateKeys decider symbols :=
    directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols key keyMember
  have candidateMember' : key ∈ StableOccurrenceRanks.candidateKeys
      (directSourceFinalAtomIdentityCodes decider symbols) := by
    rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    exact candidateMember
  simp only [groupedVariableFanSiteSlot_genericSlot]
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  exact FinalFanDataTripleAssembler.stableFan_direction_of_candidateKey
    (directSourceFinalAtomIdentityCodes decider symbols)
    (directSourceFinalVariableOccurrenceData decider symbols)
    (fun value _valueMember =>
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value)
    key candidateMember'

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataStableKeyKind
import LeanTrominoes.ListZipWithProject
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanStableSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler

/-! # Connector-kind alignment of grouped final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreeToThreeDM
open PeriodicPlanarOneInThreeToThreeDM

@[simp] theorem groupedVariableFanSiteSlot_genericSlot
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    groupedVariableFanSiteSlot (groupedVariableFanGenericSlot slot) =
      occurrenceVariableSiteSlot slot := by
  cases slot <;> rfl

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

/-- Grouped fan/slot records have the explicit stable-key normal form over
the same key column as grouped occurrence records. -/
theorem directSourceFinalGroupedVariableFanSlots_eq_map_stableFan
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanSlots decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map fun key =>
        (FinalFanDataTripleAssembler.stableFan
            (directSourceFinalOccurrenceCandidateKeys decider symbols)
            (directSourceFinalVariableOccurrenceData decider symbols)
            (key / 3)
            (BoundedPositiveCountPreds.boundedPositiveCountPred
              ((directSourceFinalAtomIdentityCodes decider symbols).count
                (key / 3))),
          groupedVariableFanGenericSlot
            (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_zipWith,
    directSourceFinalGroupedVariableFanData_eq_map_stableFan,
    directSourceFinalGroupedOccurrenceSlots_eq_map_mod]
  exact List.zipWith_map_map_same _ _ _ _

/-- Every grouped fan/slot selects the connector kind stored in its aligned
finite occurrence record. -/
theorem directSourceFinalGroupedVariableFanSlotKinds
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun pair data =>
        pair.1.kind (groupedVariableFanSiteSlot pair.2) = data.kind)
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
  exact FinalFanDataTripleAssembler.stableFan_kind_of_candidateKey
    (directSourceFinalAtomIdentityCodes decider symbols)
    (directSourceFinalVariableOccurrenceData decider symbols)
    (fun value _valueMember =>
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value)
    key candidateMember'

end LeanTrominoes.PeriodicCNFStripReduction

end

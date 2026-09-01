/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentityOccurrenceBound
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotPermutation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanCountPredSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceSelectorMultiplicity
import LeanTrominoes.StableOccurrenceRanksActiveSlots

/-! # Active slots of grouped direct final variable fans -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreeToThreeDM
open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every compiled source occurrence slot is below its aligned multiplicity
predecessor. -/
theorem directSourceFinalOccurrenceSlots_countPreds_active
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun slot countPred => slot.index < countPred.val + 1)
      (directSourceFinalOccurrenceSlots decider symbols)
      (directSourceFinalOccurrenceCountPreds decider symbols) := by
  unfold directSourceFinalOccurrenceSlots
  rw [directSourceFinalOccurrenceStableRanks_eq_identityCodes,
    directSourceFinalOccurrenceCountPreds_eq_identityCodes]
  apply StableOccurrenceRanks.slots_countPreds_active_of_count_le_three
  intro value _valueMember
  exact directSourceFinalAtomIdentityCodes_count_le_three
    decider symbols value

private theorem fans_slots_active_of_countPreds
    {fans : List VariableRibbonFanData}
    {slots : List PeriodicOneInThreeToThreeDM.OccurrenceSlot}
    (active : List.Forall₂
      (fun slot countPred => slot.index < countPred.val + 1)
      slots (fans.map fun fan => fan.countPred)) :
    List.Forall₂
      (fun fan slot => slot.index < fan.countPred.val + 1)
      fans slots := by
  induction fans generalizing slots with
  | nil =>
      cases active
      exact List.Forall₂.nil
  | cons fan fans induction =>
      cases slots with
      | nil => cases active
      | cons slot slots =>
          cases active with
          | cons head rest =>
              exact List.Forall₂.cons head (induction rest)

/-- The compiled fan record and occurrence-slot columns are pointwise
aligned on active slots. -/
theorem directSourceFinalVariableFans_slots_active
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun fan slot => slot.index < fan.countPred.val + 1)
      (directSourceFinalVariableFanData decider symbols)
      (directSourceFinalOccurrenceSlots decider symbols) := by
  apply fans_slots_active_of_countPreds
  rw [directSourceFinalVariableFanData_countPreds]
  exact directSourceFinalOccurrenceSlots_countPreds_active
    decider symbols

private theorem zipWith_fan_slot_active
    {fans : List VariableRibbonFanData}
    {slots : List PeriodicOneInThreeToThreeDM.OccurrenceSlot}
    (aligned : List.Forall₂
      (fun fan slot => slot.index < fan.countPred.val + 1)
      fans slots) :
    ∀ pair ∈ List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        fans slots,
      (VariableIncidenceLocalControl.ofPair pair).IsActive := by
  induction aligned with
  | nil => simp
  | @cons fan slot fans slots head rest induction =>
      intro pair pairMember
      simp only [List.zipWith_cons_cons, List.mem_cons] at pairMember
      rcases pairMember with pairEq | pairMember
      · subst pair
        change
          (groupedVariableFanSiteSlot
            (groupedVariableFanGenericSlot slot)).index <
            fan.countPred.val + 1
        cases slot <;> exact head
      · exact induction pair pairMember

/-- Every pair in the original clause-major fan/slot columns selects an
active variable occurrence. -/
theorem directSourceFinalCandidateVariableFanSlots_active
    (symbols : List encoding.Γ) :
    ∀ pair ∈ List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        (directSourceFinalVariableFanData decider symbols)
        (directSourceFinalOccurrenceSlots decider symbols),
      (VariableIncidenceLocalControl.ofPair pair).IsActive := by
  exact zipWith_fan_slot_active
    (directSourceFinalVariableFans_slots_active decider symbols)

/-- Stable occurrence regrouping preserves activity of every finite
variable-fan slot. -/
theorem directSourceFinalGroupedVariableFanSlots_active
    (symbols : List encoding.Γ) :
    ∀ pair ∈ directSourceFinalGroupedVariableFanSlots decider symbols,
      (VariableIncidenceLocalControl.ofPair pair).IsActive := by
  intro pair pairMember
  apply directSourceFinalCandidateVariableFanSlots_active
    decider symbols pair
  exact (directSourceFinalGroupedVariableFanSlots_perm_candidateColumns
    decider symbols).mem_iff.mp pairMember

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteRoleSlotUnaryDecoderCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanDataSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataCode
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Aligned grouped variable-fan and occurrence-slot records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM

abbrev GroupedVariableFanSlot :=
  FiniteRoleSlotUnaryDecoder.Pair VariableRibbonFanData

noncomputable local instance : Inhabited VariableRibbonFanData :=
  ⟨variableRibbonFanDataOfCode default⟩

/-- Embed a source occurrence slot into the decoder's eight finite slots. -/
def groupedVariableFanGenericSlot
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    FiniteRoleSlotUnaryDecoder.Slot :=
  ⟨slot.index, by
    cases slot <;>
      simp [PeriodicOneInThreeToThreeDM.OccurrenceSlot.index]⟩

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariableFanSlotStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Decoder role bases for the grouped complete variable-fan records. -/
def directSourceFinalGroupedVariableFanRoleBases
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values
    (fun fan : VariableRibbonFanData =>
      8 * (Fintype.equivFin VariableRibbonFanData fan).val)
    (directSourceFinalGroupedVariableFanData decider symbols)

/-- Decoder slot numbers aligned with the grouped fan records. -/
def directSourceFinalGroupedVariableFanSlotValues
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values
    (fun slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot =>
      (groupedVariableFanGenericSlot slot).val)
    (directSourceFinalGroupedOccurrenceSlots decider symbols)

/-- Unary role/slot codes for every grouped active occurrence. -/
def directSourceFinalGroupedVariableFanSlotCodes
    (symbols : List encoding.Γ) : List Nat :=
  AlignedUnaryListClosure.added
    (directSourceFinalGroupedVariableFanRoleBases decider symbols)
    (directSourceFinalGroupedVariableFanSlotValues decider symbols)

/-- Complete finite fan data paired with the active occurrence slot that
selects the current variable module. -/
def directSourceFinalGroupedVariableFanSlots
    (symbols : List encoding.Γ) : List GroupedVariableFanSlot :=
  FiniteRoleSlotUnaryDecoder.pairs
    (Role := VariableRibbonFanData)
    (directSourceFinalGroupedVariableFanSlotCodes decider symbols)

@[simp] theorem directSourceFinalGroupedVariableFanRoleBases_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanRoleBases decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedVariableFanRoleBases
    FiniteUnaryFieldMap.values
  rw [List.length_map,
    directSourceFinalGroupedVariableFanData_length]

@[simp] theorem directSourceFinalGroupedVariableFanSlotValues_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanSlotValues decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  unfold directSourceFinalGroupedVariableFanSlotValues
    FiniteUnaryFieldMap.values
  rw [List.length_map,
    directSourceFinalGroupedOccurrenceSlots_length]

noncomputable def
    directSourceFinalGroupedVariableFanRoleBasesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableFanRoleBases decider) := by
  unfold directSourceFinalGroupedVariableFanRoleBases
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanDataComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime fun fan : VariableRibbonFanData =>
      8 * (Fintype.equivFin VariableRibbonFanData fan).val)

noncomputable def
    directSourceFinalGroupedVariableFanSlotValuesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableFanSlotValues decider) := by
  unfold directSourceFinalGroupedVariableFanSlotValues
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedOccurrenceSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      fun slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot =>
      (groupedVariableFanGenericSlot slot).val)

/-- The aligned finite fan/slot codes compile in polynomial time. -/
noncomputable def
    directSourceFinalGroupedVariableFanSlotCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableFanSlotCodes decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedVariableFanSlotCodes
    exact AlignedUnaryListClosure.addedComputableInPolyTime
      id
      (directSourceFinalGroupedVariableFanRoleBases decider)
      (directSourceFinalGroupedVariableFanSlotValues decider)
      (fun symbols => by
        rw [directSourceFinalGroupedVariableFanRoleBases_length,
          directSourceFinalGroupedVariableFanSlotValues_length])
      (directSourceFinalGroupedVariableFanRoleBasesComputableInPolyTime
        decider)
      (directSourceFinalGroupedVariableFanSlotValuesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

/-- The paired grouped variable-fan/slot records compile in polynomial
time. -/
noncomputable def
    directSourceFinalGroupedVariableFanSlotsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableFanSlots decider) := by
  unfold directSourceFinalGroupedVariableFanSlots
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanSlotCodesComputableInPolyTime decider)
    (FiniteRoleSlotUnaryDecoder.computableInPolyTime
      (Role := VariableRibbonFanData))

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotCompiler

/-! # Semantics of aligned grouped variable-fan and occurrence-slot records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

noncomputable local instance : Inhabited VariableRibbonFanData :=
  ⟨variableRibbonFanDataOfCode default⟩

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The physical unary addition is pointwise role-base/slot addition. -/
theorem directSourceFinalGroupedVariableFanSlotCodes_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanSlotCodes decider symbols =
      List.zipWith (· + ·)
        (directSourceFinalGroupedVariableFanRoleBases decider symbols)
        (directSourceFinalGroupedVariableFanSlotValues decider symbols) := by
  unfold directSourceFinalGroupedVariableFanSlotCodes
    AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by
    rw [directSourceFinalGroupedVariableFanRoleBases_length,
      directSourceFinalGroupedVariableFanSlotValues_length])

private theorem decode_groupedVariableFanSlot
    (fan : VariableRibbonFanData)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    FiniteRoleSlotUnaryDecoder.decode
        (FiniteRoleSlotUnaryDecoder.boundedCode
          (8 * (Fintype.equivFin VariableRibbonFanData fan).val +
            (groupedVariableFanGenericSlot slot).val)) =
      (fan, groupedVariableFanGenericSlot slot) := by
  exact FiniteRoleSlotUnaryDecoder.decode_role_slot_index
    fan (groupedVariableFanGenericSlot slot)

private theorem pairs_zipWith_codes
    (fans : List VariableRibbonFanData)
    (slots : List PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    FiniteRoleSlotUnaryDecoder.pairs
        (Role := VariableRibbonFanData)
        (List.zipWith (· + ·)
          (FiniteUnaryFieldMap.values
            (fun fan : VariableRibbonFanData =>
              8 * (Fintype.equivFin VariableRibbonFanData fan).val) fans)
          (FiniteUnaryFieldMap.values
            (fun slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot =>
              (groupedVariableFanGenericSlot slot).val) slots)) =
      List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        fans slots := by
  induction fans generalizing slots with
  | nil => rfl
  | cons fan fans induction =>
      cases slots with
      | nil => rfl
      | cons slot slots =>
          simp only [FiniteUnaryFieldMap.values, List.map_cons,
            List.zipWith_cons_cons]
          change
            FiniteRoleSlotUnaryDecoder.decode
                (FiniteRoleSlotUnaryDecoder.boundedCode
                  (8 * (Fintype.equivFin VariableRibbonFanData fan).val +
                    (groupedVariableFanGenericSlot slot).val)) ::
                FiniteRoleSlotUnaryDecoder.pairs
                  (List.zipWith (· + ·)
                    (FiniteUnaryFieldMap.values
                      (fun fan : VariableRibbonFanData =>
                        8 * (Fintype.equivFin
                          VariableRibbonFanData fan).val) fans)
                    (FiniteUnaryFieldMap.values
                      (fun slot :
                          PeriodicOneInThreeToThreeDM.OccurrenceSlot =>
                        (groupedVariableFanGenericSlot slot).val) slots)) =
              (fan, groupedVariableFanGenericSlot slot) ::
                List.zipWith
                  (fun fan slot =>
                    (fan, groupedVariableFanGenericSlot slot)) fans slots
          rw [decode_groupedVariableFanSlot, induction]

/-- Decoding the compiled role/slot fields gives exactly the aligned grouped
fan record and active source occurrence slot. -/
theorem directSourceFinalGroupedVariableFanSlots_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanSlots decider symbols =
      List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        (directSourceFinalGroupedVariableFanData decider symbols)
        (directSourceFinalGroupedOccurrenceSlots decider symbols) := by
  unfold directSourceFinalGroupedVariableFanSlots
  rw [directSourceFinalGroupedVariableFanSlotCodes_eq_zipWith]
  unfold directSourceFinalGroupedVariableFanRoleBases
    directSourceFinalGroupedVariableFanSlotValues
  exact pairs_zipWith_codes _ _

@[simp] theorem directSourceFinalGroupedVariableFanSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanSlots decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_zipWith,
    List.length_zipWith,
    directSourceFinalGroupedVariableFanData_length,
    directSourceFinalGroupedOccurrenceSlots_length, min_self]

end LeanTrominoes.PeriodicCNFStripReduction

end

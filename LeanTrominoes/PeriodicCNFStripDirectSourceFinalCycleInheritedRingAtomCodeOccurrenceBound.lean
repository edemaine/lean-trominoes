/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDistinctAtomIdentityNodup

/-! # Occurrence bound for inherited implication-cycle ring codes -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open HorizontalRoutedRouteHeaderInheritedSourceSelection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem localCycleInheritedRingAtomCodeBlock_count_le_two
    (identity target : Nat) :
    (directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.map
      (inheritedRingAtomCode identity)).count target <= 2 := by
  by_cases targetMember : target ∈
      directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.map
        (inheritedRingAtomCode identity)
  · rcases List.mem_map.mp targetMember with
      ⟨slot, slotMember, rfl⟩
    have injective : Function.Injective (inheritedRingAtomCode identity) := by
      intro first second equality
      unfold inheritedRingAtomCode at equality
      omega
    rw [List.count_map_of_injective _ _ injective slot]
    have slotLt := (List.forall_iff_forall_mem.mp
      directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues_forall_lt)
        slot slotMember
    let bounded : DirectFinalCycleRingVertexSlot := ⟨slot, slotLt⟩
    have countEq :=
      directSourceFinalLocalCycleSelectedInheritedRingVertexSlot_count_eq_two
        bounded
    simpa [bounded] using countEq.le
  · rw [List.count_eq_zero.mpr targetMember]
    omega

private theorem cycleInheritedRingAtomCodeBlocks_count_le_two
    (identities : List Nat) (identitiesNodup : identities.Nodup)
    (target : Nat) :
    (identities.flatMap fun identity =>
      directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.map
        (inheritedRingAtomCode identity)).count target <= 2 := by
  induction identities generalizing target with
  | nil => simp
  | cons identity identities induction =>
      rw [List.nodup_cons] at identitiesNodup
      simp only [List.flatMap_cons, List.count_append]
      by_cases headMember : target ∈
          directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.map
            (inheritedRingAtomCode identity)
      · rcases List.mem_map.mp headMember with
          ⟨slot, slotMember, rfl⟩
        have tailNotMember : inheritedRingAtomCode identity slot ∉
            identities.flatMap fun later =>
              directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.map
                (inheritedRingAtomCode later) := by
          intro tailMember
          rcases List.mem_flatMap.mp tailMember with
            ⟨later, laterMember, laterCodeMember⟩
          rcases List.mem_map.mp laterCodeMember with
            ⟨laterSlot, laterSlotMember, encodedEq⟩
          have slotLt := (List.forall_iff_forall_mem.mp
            directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues_forall_lt)
              slot slotMember
          have laterSlotLt := (List.forall_iff_forall_mem.mp
            directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues_forall_lt)
              laterSlot laterSlotMember
          have identitiesEq := (inheritedRingAtomCode_eq_iff
            later identity laterSlot slot laterSlotLt slotLt).mp encodedEq
          exact identitiesNodup.1 (identitiesEq.1 ▸ laterMember)
        rw [List.count_eq_zero.mpr tailNotMember, Nat.add_zero]
        exact localCycleInheritedRingAtomCodeBlock_count_le_two identity _
      · rw [List.count_eq_zero.mpr headMember, Nat.zero_add]
        exact induction identitiesNodup.2 target

/-- After inherited-position selection, each base-nine code occurs at most
twice in the entire implication-cycle suffix. -/
theorem directSourceFinalCycleSelectedInheritedRingAtomCodes_count_le_two
    (symbols : List encoding.Γ) (target : Nat) :
    (selectedInheritedValues
      (directSourceFinalCyclePresentationAtomScopeControls decider symbols)
      (directSourceFinalCycleInheritedRingAtomCodes
        decider symbols)).count target <= 2 := by
  rw [directSourceFinalCycleSelectedInheritedRingAtomCodes_eq_flatMap]
  exact cycleInheritedRingAtomCodeBlocks_count_le_two
    (directSourceFinalDistinctAtomIdentityIndices decider symbols)
    (directSourceFinalDistinctAtomIdentityIndices_nodup decider symbols)
    target

end LeanTrominoes.PeriodicCNFStripReduction

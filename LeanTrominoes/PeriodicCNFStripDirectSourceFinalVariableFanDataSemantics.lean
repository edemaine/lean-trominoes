/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanOccurrenceDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanDataCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of complete direct final variable-fan data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Count predecessors repeated three times, still retaining their finite
type before generic role/slot encoding. -/
def directSourceFinalFanRepeatedCountPreds
    (symbols : List encoding.Γ) : List (Fin 3) :=
  (directSourceFinalOccurrenceCountPreds decider symbols).flatMap
    fun countPred => List.replicate 3 countPred

/-- The three uniquely keyed occurrence records paired with the repeated fan
count belonging to their original final occurrence. -/
def directSourceFinalFanSelectedCountedOccurrencesExpected
    (symbols : List encoding.Γ) :
    List (FinalFanOccurrenceData × Fin 3) :=
  List.zipWith Prod.mk
    (directSourceFinalFanSelectedOccurrenceDataExpected decider symbols)
    (directSourceFinalFanRepeatedCountPreds decider symbols)

/-- Declarative fan-data result obtained by decoding those exact counted
occurrences and grouping consecutive triples. -/
def directSourceFinalVariableFanDataExpected
    (symbols : List encoding.Γ) :
    List PeriodicPlanarOneInThreeToThreeDM.VariableRibbonFanData :=
  FinalFanDataTripleAssembler.output
    ((directSourceFinalFanSelectedCountedOccurrencesExpected
      decider symbols).map fun pair =>
        (pair.1, FinalFanDataTripleAssembler.slotOfCountPred pair.2))

/-- The unary natural count column is precisely the finite repeated-count
column mapped through `Fin.val`. -/
theorem directSourceFinalFanRepeatedCountPredValues_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalFanRepeatedCountPredValues decider symbols =
      (directSourceFinalFanRepeatedCountPreds decider symbols).map Fin.val := by
  unfold directSourceFinalFanRepeatedCountPredValues
    directSourceFinalFanCountPredValues
    directSourceFinalFanRepeatedCountPreds
    UnaryFieldFixedCopies.values
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro countPred countPredMember
  simp

private theorem zipWith_map_map_pairCode
    (data : List FinalFanOccurrenceData) (countPreds : List (Fin 3)) :
    List.zipWith (fun first second => first + second)
        (data.map finalFanOccurrenceDataCode)
        (countPreds.map Fin.val) =
      (List.zipWith Prod.mk data countPreds).map fun pair =>
        finalFanOccurrenceDataCode pair.1 + pair.2.val := by
  induction data generalizing countPreds with
  | nil => rfl
  | cons occurrence data induction =>
      cases countPreds with
      | nil => rfl
      | cons countPred countPreds => simp [induction]

/-- Before decoding, the compiled added codes are exactly role codes plus
their aligned finite fan-count slots. -/
theorem directSourceFinalFanOccurrencePairCodes_eq_expected_map
    (symbols : List encoding.Γ) :
    directSourceFinalFanOccurrencePairCodes decider symbols =
      (directSourceFinalFanSelectedCountedOccurrencesExpected
        decider symbols).map fun pair =>
          finalFanOccurrenceDataCode pair.1 + pair.2.val := by
  unfold directSourceFinalFanOccurrencePairCodes
    AlignedUnaryListClosure.added
  rw [UnaryAlignedAddMachine.sums_eq_zipWith
    (UnaryAlignedAddMachine.Valid.of_length_eq (by
      rw [directSourceFinalFanSelectedOccurrenceCodes_length,
        directSourceFinalFanRepeatedCountPredValues_length]))]
  rw [directSourceFinalFanSelectedOccurrenceCodes_eq_expected_map,
    directSourceFinalFanRepeatedCountPredValues_eq_map]
  unfold directSourceFinalFanSelectedCountedOccurrencesExpected
  exact zipWith_map_map_pairCode _ _

private theorem decode_finalFanOccurrenceData_countPred
    (pair : FinalFanOccurrenceData × Fin 3) :
    FiniteRoleSlotUnaryDecoder.decode
        (FiniteRoleSlotUnaryDecoder.boundedCode
          (finalFanOccurrenceDataCode pair.1 + pair.2.val)) =
      (pair.1, FinalFanDataTripleAssembler.slotOfCountPred pair.2) := by
  change FiniteRoleSlotUnaryDecoder.decode
      (FiniteRoleSlotUnaryDecoder.boundedCode
        (8 * (Fintype.equivFin FinalFanOccurrenceData pair.1).val +
          (FinalFanDataTripleAssembler.slotOfCountPred pair.2).val)) = _
  exact FiniteRoleSlotUnaryDecoder.decode_role_slot_index
    pair.1 (FinalFanDataTripleAssembler.slotOfCountPred pair.2)

/-- Generic finite decoding recovers exactly the selected occurrence record
and its repeated bounded fan count. -/
theorem directSourceFinalFanOccurrencePairs_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalFanOccurrencePairs decider symbols =
      (directSourceFinalFanSelectedCountedOccurrencesExpected
        decider symbols).map fun pair =>
          (pair.1, FinalFanDataTripleAssembler.slotOfCountPred pair.2) := by
  unfold directSourceFinalFanOccurrencePairs
    FiniteRoleSlotUnaryDecoder.pairs
  rw [directSourceFinalFanOccurrencePairCodes_eq_expected_map,
    List.map_map]
  apply List.map_congr_left
  intro pair pairMember
  exact decode_finalFanOccurrenceData_countPred pair

/-- The complete compiled variable-fan column is the declarative grouping of
the three uniquely keyed occurrence records and their original occurrence's
count predecessor. -/
theorem directSourceFinalVariableFanData_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalVariableFanData decider symbols =
      directSourceFinalVariableFanDataExpected decider symbols := by
  unfold directSourceFinalVariableFanData
    directSourceFinalVariableFanDataExpected
  rw [directSourceFinalFanOccurrencePairs_eq_expected]

end LeanTrominoes.PeriodicCNFStripReduction

end

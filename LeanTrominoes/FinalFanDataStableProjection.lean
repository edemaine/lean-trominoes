/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataTripleAssembler
import LeanTrominoes.FinalFanQueryRankKeyCoverage
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.ListZipWithFlatMapAligned

/-! # Stable-key projection from assembled finite fan data -/

noncomputable section

namespace LeanTrominoes.FinalFanDataTripleAssembler

open PeriodicCNFStripReduction
open PeriodicOneInThreeToThreeDM
open PlanarThreeDM

/-- Select one finite occurrence record by an identity and finite fan slot,
using the same inactive-slot fallback as the compiler. -/
def stableSelectedOccurrence
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (value : Nat) (countPred slot : Fin 3) : OccurrenceData :=
  FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
    (value * 3 + (FinalFanQueryRanks.selectedRank countPred slot).val)

/-- The semantic fan assembled from the three stable rank queries of one
presented identity. -/
def stableFan (candidateKeys : List Nat) (records : List OccurrenceData)
    (value : Nat) (countPred : Fin 3) : FanData :=
  fanData countPred
    (stableSelectedOccurrence candidateKeys records value countPred 0)
    (stableSelectedOccurrence candidateKeys records value countPred 1)
    (stableSelectedOccurrence candidateKeys records value countPred 2)

/-- The exact three decoded occurrence/count pairs consumed to build one
semantic fan. -/
def stableFanPairBlock
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (value : Nat) (countPred : Fin 3) : List Pair :=
  (FinalFanQueryRanks.block countPred).map fun rank =>
    (FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
        (value * 3 + rank.val),
      slotOfCountPred countPred)

/-- Consecutive semantic pair blocks assemble to the corresponding semantic
fan map. -/
theorem grouped_flatMap_stableFanPairBlock
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (countPred : Nat → Fin 3) (values : List Nat) :
    grouped (values.flatMap fun value =>
        stableFanPairBlock candidateKeys records value (countPred value)) =
      values.map fun value =>
        stableFan candidateKeys records value (countPred value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.flatMap_cons, List.map_cons]
      rw [show stableFanPairBlock candidateKeys records value
            (countPred value) =
          [(stableSelectedOccurrence candidateKeys records value
              (countPred value) 0, slotOfCountPred (countPred value)),
            (stableSelectedOccurrence candidateKeys records value
              (countPred value) 1, slotOfCountPred (countPred value)),
            (stableSelectedOccurrence candidateKeys records value
              (countPred value) 2, slotOfCountPred (countPred value))] by
        rfl]
      simp only [List.cons_append, List.nil_append, grouped,
        countPredOfSlot_slotOfCountPred]
      change stableFan candidateKeys records value (countPred value) ::
          grouped (values.flatMap fun later =>
            stableFanPairBlock candidateKeys records later
              (countPred later)) =
        stableFan candidateKeys records value (countPred value) ::
          values.map fun later =>
            stableFan candidateKeys records later (countPred later)
      rw [induction]

/-- Zipping the stable selected-record blocks with three repeated count
predecessors, then applying the decoder-slot embedding, gives exactly the
semantic pair blocks. -/
theorem map_zip_stableSelected_replicate
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (countPred : Nat → Fin 3) (values : List Nat) :
    (List.zipWith Prod.mk
      (values.flatMap fun value =>
        (FinalFanQueryRanks.block (countPred value)).map fun rank =>
          FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
            (value * 3 + rank.val))
      (values.flatMap fun value => List.replicate 3 (countPred value))).map
        (fun pair => (pair.1, slotOfCountPred pair.2)) =
      values.flatMap fun value =>
        stableFanPairBlock candidateKeys records value (countPred value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.flatMap_cons]
      rw [List.zipWith_append_of_length_eq Prod.mk
        ((FinalFanQueryRanks.block (countPred value)).map fun rank =>
          FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
            (value * 3 + rank.val))
        (values.flatMap fun later =>
          (FinalFanQueryRanks.block (countPred later)).map fun rank =>
            FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
              (later * 3 + rank.val))
        (List.replicate 3 (countPred value))
        (values.flatMap fun later => List.replicate 3 (countPred later))
        (by simp)]
      simp only [List.map_append]
      rw [induction]
      congr 1

/-- Every active finite slot of the semantic fan projects the occurrence
record at that exact stable rank. -/
theorem stableFan_kind_of_active
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (value : Nat) (countPred : Fin 3) (slot : VariableSiteSlot)
    (active : slot.index < countPred.val + 1) :
    (stableFan candidateKeys records value countPred).kind slot =
      (FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
        (value * 3 + slot.index)).kind := by
  cases countPred using Fin.cases with
  | zero =>
      cases slot <;>
        simp [stableFan, stableSelectedOccurrence, fanData,
          FinalFanQueryRanks.selectedRank,
          VariableSiteSlot.index] at active ⊢
  | succ countPred =>
      cases countPred using Fin.cases with
      | zero =>
          cases slot <;>
            simp [stableFan, stableSelectedOccurrence, fanData,
              FinalFanQueryRanks.selectedRank,
              VariableSiteSlot.index] at active ⊢
      | succ countPred =>
          have countPredEq : countPred = 0 := Fin.eq_zero countPred
          subst countPred
          cases slot <;>
            simp [stableFan, stableSelectedOccurrence, fanData,
              FinalFanQueryRanks.selectedRank,
              VariableSiteSlot.index]

/-- Every active finite slot of the semantic fan projects the polarity of the
occurrence record at that exact stable rank. -/
theorem stableFan_polarity_of_active
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (value : Nat) (countPred : Fin 3) (slot : VariableSiteSlot)
    (active : slot.index < countPred.val + 1) :
    (stableFan candidateKeys records value countPred).polarity slot =
      (FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
        (value * 3 + slot.index)).polarity := by
  cases countPred using Fin.cases with
  | zero =>
      cases slot <;>
        simp [stableFan, stableSelectedOccurrence, fanData,
          FinalFanQueryRanks.selectedRank,
          VariableSiteSlot.index] at active ⊢
  | succ countPred =>
      cases countPred using Fin.cases with
      | zero =>
          cases slot <;>
            simp [stableFan, stableSelectedOccurrence, fanData,
              FinalFanQueryRanks.selectedRank,
              VariableSiteSlot.index] at active ⊢
      | succ countPred =>
          have countPredEq : countPred = 0 := Fin.eq_zero countPred
          subst countPred
          cases slot <;>
            simp [stableFan, stableSelectedOccurrence, fanData,
              FinalFanQueryRanks.selectedRank,
              VariableSiteSlot.index]

/-- Every active finite slot of the semantic fan projects the direction of the
occurrence record at that exact stable rank. -/
theorem stableFan_direction_of_active
    (candidateKeys : List Nat) (records : List OccurrenceData)
    (value : Nat) (countPred : Fin 3) (slot : VariableSiteSlot)
    (active : slot.index < countPred.val + 1) :
    (stableFan candidateKeys records value countPred).direction slot =
      (FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys records
        (value * 3 + slot.index)).direction := by
  cases countPred using Fin.cases with
  | zero =>
      cases slot <;>
        simp [stableFan, stableSelectedOccurrence, fanData,
          FinalFanQueryRanks.selectedRank,
          VariableSiteSlot.index] at active ⊢
  | succ countPred =>
      cases countPred using Fin.cases with
      | zero =>
          cases slot <;>
            simp [stableFan, stableSelectedOccurrence, fanData,
              FinalFanQueryRanks.selectedRank,
              VariableSiteSlot.index] at active ⊢
      | succ countPred =>
          have countPredEq : countPred = 0 := Fin.eq_zero countPred
          subst countPred
          cases slot <;>
            simp [stableFan, stableSelectedOccurrence, fanData,
              FinalFanQueryRanks.selectedRank,
              VariableSiteSlot.index]

end LeanTrominoes.FinalFanDataTripleAssembler

end

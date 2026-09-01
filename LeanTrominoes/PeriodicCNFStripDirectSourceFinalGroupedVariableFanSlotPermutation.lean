/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyPermutation

/-! # Exact reordering of grouped fan/slot records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

private theorem zipWith_map_map
    {Key First Second Target : Type*}
    (combine : First → Second → Target)
    (first : Key → First) (second : Key → Second)
    (keys : List Key) :
    List.zipWith combine (keys.map first) (keys.map second) =
      keys.map fun key => combine (first key) (second key) := by
  induction keys with
  | nil => rfl
  | cons key keys induction => simp [induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Grouped fan/slot records are exactly a permutation of their original
clause-major candidate columns.  In particular, all finite local data stays
attached to the same occurrence while the key compiler changes order. -/
theorem directSourceFinalGroupedVariableFanSlots_perm_candidateColumns
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanSlots decider symbols).Perm
      (List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        (directSourceFinalVariableFanData decider symbols)
        (directSourceFinalOccurrenceSlots decider symbols)) := by
  let keys := directSourceFinalOccurrenceCandidateKeys decider symbols
  let queries := directSourceFinalUniqueFanQueryKeys decider symbols
  let fans := directSourceFinalVariableFanData decider symbols
  let slots := directSourceFinalOccurrenceSlots decider symbols
  let fanDatum :=
    FiniteAlphabetKeyedValueLookup.alignedDatum keys fans
  let slotDatum :=
    FiniteAlphabetKeyedValueLookup.alignedDatum keys slots
  have keysNodup : keys.Nodup :=
    directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  have keysFansLength : keys.length = fans.length := by
    simp [keys, fans]
  have keysSlotsLength : keys.length = slots.length := by
    simp [keys, slots]
  have fansEq : fans = keys.map fanDatum := by
    exact FiniteAlphabetKeyedValueLookup.candidateValues_eq_map_alignedDatum
      keys fans keysFansLength keysNodup
  have slotsEq : slots = keys.map slotDatum := by
    exact FiniteAlphabetKeyedValueLookup.candidateValues_eq_map_alignedDatum
      keys slots keysSlotsLength keysNodup
  rw [directSourceFinalGroupedVariableFanSlots_eq_zipWith,
    directSourceFinalGroupedVariableFanData_eq_map_alignedDatum,
    directSourceFinalGroupedOccurrenceSlots_eq_map_alignedDatum]
  change
    (List.zipWith
      (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
      (queries.map fanDatum) (queries.map slotDatum)).Perm _
  rw [zipWith_map_map]
  calc
    (queries.map fun key =>
        (fanDatum key, groupedVariableFanGenericSlot (slotDatum key))).Perm
        (keys.map fun key =>
          (fanDatum key,
            groupedVariableFanGenericSlot (slotDatum key))) :=
      (directSourceFinalUniqueFanQueryKeys_perm_candidateKeys
        decider symbols).map _
    _ = List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        (keys.map fanDatum) (keys.map slotDatum) := by
      rw [zipWith_map_map]
    _ = List.zipWith
        (fun fan slot => (fan, groupedVariableFanGenericSlot slot))
        fans slots := by rw [← fansEq, ← slotsEq]

end LeanTrominoes.PeriodicCNFStripReduction

end

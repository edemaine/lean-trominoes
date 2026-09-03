/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceBodyBlockAlignmentSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyLocalitySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceOccurrenceBlockIndexSemantics

/-! # Local routed-body lookup inside one grouped occurrence -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open GroupedRoutedIncidenceKeyLocality

/-- Complete bodies of one grouped occurrence, expressed using only its
three local routed keys and its aligned RGB body block. -/
def groupedVariableIncidenceLocalBodyBlock
    (start : Nat) (pair : GroupedVariableFanSlot)
    (data : FinalFanOccurrenceData)
    (bodyBlock : List (List AxisDirection)) :
    List (List AxisDirection) :=
  (groupedVariableIncidencePrefixQueryBlock pair).zipIdx (3 * start) |>.map
    fun tagged =>
      HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
        if tagged.2 ∈ keyBlock start data then
          FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            (keyBlock start data) bodyBlock tagged.2
        else []

private theorem keyBlock_nodup
    (start : Nat) (data : FinalFanOccurrenceData) :
    (keyBlock start data).Nodup := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  cases kind <;>
    simp [keyBlock, directFinalOccurrenceRoutedIncidenceKeyOffsets]

private theorem function_eq_on_of_map_eq
    {Key Value : Type*} [DecidableEq Key]
    (keys : List Key) (first second : Key → Value)
    (mapsEq : keys.map first = keys.map second)
    (key : Key) (keyMember : key ∈ keys) :
    first key = second key := by
  induction keys with
  | nil => simp at keyMember
  | cons head keys induction =>
      have parts := List.cons.inj mapsEq
      rcases (List.mem_cons.mp keyMember) with rfl | keyMember
      · exact parts.1
      · exact induction parts.2 keyMember

/-- If the global key/body table is block-aligned and global membership is
local on the current interval, the global sparse lookup reduces exactly to
the occurrence-local three-key lookup. -/
theorem groupedVariableIncidenceGlobalBodyBlock_eq_local
    (globalKeys : List Nat) (globalBodies : List (List AxisDirection))
    (start : Nat) (pair : GroupedVariableFanSlot)
    (data : FinalFanOccurrenceData)
    (bodyBlock : List (List AxisDirection))
    (bodyAligned :
      (keyBlock start data).map
          (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            globalKeys globalBodies) = bodyBlock)
    (membershipLocal : ∀ tagged ∈
      (groupedVariableIncidencePrefixQueryBlock pair).zipIdx (3 * start),
      tagged.2 ∈ globalKeys ↔ tagged.2 ∈ keyBlock start data) :
    ((groupedVariableIncidencePrefixQueryBlock pair).zipIdx
        (3 * start)).map (fun tagged =>
          HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
            if tagged.2 ∈ globalKeys then
              FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
                globalKeys globalBodies tagged.2
            else []) =
      groupedVariableIncidenceLocalBodyBlock start pair data bodyBlock := by
  let globalBody :=
    FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
      globalKeys globalBodies
  let localBody :=
    FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
      (keyBlock start data) bodyBlock
  have alignedLength : (keyBlock start data).length = bodyBlock.length := by
    rw [← bodyAligned]
    simp
  have localCanonical :
      bodyBlock = (keyBlock start data).map localBody :=
    FiniteAlphabetKeyedDelimitedBlockLookup.bodies_eq_map_alignedBody
      (keyBlock start data) bodyBlock alignedLength
      (keyBlock_nodup start data)
  have bodyMaps :
      (keyBlock start data).map globalBody =
        (keyBlock start data).map localBody :=
    bodyAligned.trans localCanonical
  unfold groupedVariableIncidenceLocalBodyBlock
  apply List.map_congr_left
  intro tagged taggedMember
  by_cases globalRouted : tagged.2 ∈ globalKeys
  · have localRouted :=
      (membershipLocal tagged taggedMember).mp globalRouted
    have lookupEq :
        FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            globalKeys globalBodies tagged.2 =
          FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            (keyBlock start data) bodyBlock tagged.2 := by
      simpa [globalBody, localBody] using
        (function_eq_on_of_map_eq
        (keyBlock start data) globalBody localBody bodyMaps
        tagged.2 localRouted)
    rw [if_pos globalRouted, if_pos localRouted, lookupEq]
  · have localNotRouted : tagged.2 ∉ keyBlock start data := by
      intro localRouted
      exact globalRouted
        ((membershipLocal tagged taggedMember).mpr localRouted)
    simp [globalRouted, localNotRouted]

/-- The same reduction follows from interval locality: stable indexing puts
every query inside the current occurrence interval, whose width is fixed by
the aligned connector kind. -/
theorem groupedVariableIncidenceGlobalBodyBlock_eq_local_of_interval
    (globalKeys : List Nat) (globalBodies : List (List AxisDirection))
    (start : Nat) (pair : GroupedVariableFanSlot)
    (data : FinalFanOccurrenceData)
    (bodyBlock : List (List AxisDirection))
    (kindEq :
      pair.1.kind (groupedVariableFanSiteSlot pair.2) = data.kind)
    (bodyAligned :
      (keyBlock start data).map
          (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            globalKeys globalBodies) = bodyBlock)
    (intervalLocal : ∀ query,
      start * 3 ≤ query →
      query < (start + directFinalOccurrenceTripleBlockWidth data) * 3 →
      (query ∈ globalKeys ↔ query ∈ keyBlock start data)) :
    ((groupedVariableIncidencePrefixQueryBlock pair).zipIdx
        (3 * start)).map (fun tagged =>
          HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
            if tagged.2 ∈ globalKeys then
              FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
                globalKeys globalBodies tagged.2
            else []) =
      groupedVariableIncidenceLocalBodyBlock start pair data bodyBlock := by
  apply groupedVariableIncidenceGlobalBodyBlock_eq_local
    globalKeys globalBodies start pair data bodyBlock bodyAligned
  intro tagged taggedMember
  have lower := List.le_snd_of_mem_zipIdx taggedMember
  have upper := List.snd_lt_of_mem_zipIdx taggedMember
  rw [groupedVariableIncidencePrefixQueryBlock_length_eq_occurrenceWidth
    pair data kindEq] at upper
  exact intervalLocal tagged.2 (by simpa [Nat.mul_comm] using lower)
    (by omega)

end LeanTrominoes.PeriodicCNFStripReduction

end

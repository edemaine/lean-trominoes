/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkTargetIndexEnumeration
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration

/-! # Exact target indices of source occurrence-cycle links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedTargetIndices

def occurrenceGroups {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (List (ThreeOccurrenceVariable Variable)) :=
  (sourceVariables source).map (occurrenceVariables source)

theorem occurrenceGroups_flatten_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceGroups source).flatten.Nodup := by
  change ((sourceVariables source).flatMap
    (occurrenceVariables source)).Nodup
  rw [List.nodup_flatMap]
  constructor
  · intro atom _
    exact occurrenceVariables_nodup source atom
  · have variablesNodup : (sourceVariables source).Nodup := by
      unfold sourceVariables
      exact List.nodup_dedup _
    refine variablesNodup.imp ?_
    intro first second different
    change List.Disjoint (occurrenceVariables source first)
      (occurrenceVariables source second)
    rw [List.disjoint_left]
    intro copy firstMember secondMember
    have firstEq := occurrenceVariables_fst source first firstMember
    have secondEq := occurrenceVariables_fst source second secondMember
    exact different (firstEq.symm.trans secondEq)

@[simp] theorem occurrenceGroups_groupedLinks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    groupedLinks (occurrenceGroups source) = allCycleLinks source := by
  simp [groupedLinks, occurrenceGroups, allCycleLinks,
    List.flatMap_map]

@[simp] theorem occurrenceGroups_groupedRotated
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    groupedRotated (occurrenceGroups source) =
      rotatedOccurrenceVariables source := by
  simp [groupedRotated, rotatedGroup, occurrenceGroups,
    rotatedOccurrenceVariables, rotatedOccurrenceVariablesFor,
    List.flatMap_map]

@[simp] theorem occurrenceGroups_lengths
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceGroups source).map List.length =
      (sourceVariables source).map fun atom =>
        (occurrenceVariables source atom).length := by
  simp [occurrenceGroups, List.map_map, Function.comp_def]

@[simp] theorem occurrenceGroups_flatten_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceGroups source).flatten.length =
      PeriodicCNF.presentationLiteralCount source := by
  rw [List.length_flatten]
  simp only [occurrenceGroups_lengths]
  exact occurrenceVariables_total_length source |>.trans
    (taggedLiterals_length source)

/-- The target of each negative source incidence is the right-rotated index
of that link's source copy, exactly in grouped-emitter order. -/
theorem allCycleLinks_sourceTargetIndices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (allCycleLinks source).map (fun link =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq link.1
          (rotatedOccurrenceVariables source)) =
      PeriodicCNF.SourceCycleLinkTargetIndices.targetIndices
        ((sourceVariables source).map fun atom =>
          (occurrenceVariables source atom).length) := by
  have grouped := sourceTargetIndices_grouped_aux
    (occurrenceGroups source) (occurrenceGroups_flatten_nodup source) 0
  simpa [PeriodicCNF.SourceCycleLinkTargetIndices.targetIndices] using grouped

/-- The target endpoint of link `i` is variable vertex `i` in the rotated
occurrence-variable enumeration. -/
theorem allCycleLinks_targetTargetIndices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (allCycleLinks source).map (fun link =>
        @List.idxOf (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq link.2
          (rotatedOccurrenceVariables source)) =
      List.range (PeriodicCNF.presentationLiteralCount source) := by
  have grouped := targetIndices_grouped_aux
    (occurrenceGroups source) (occurrenceGroups_flatten_nodup source) 0
  rw [← occurrenceGroups_flatten_length source]
  simp only [occurrenceGroups_groupedLinks,
    occurrenceGroups_groupedRotated, zero_add] at grouped
  change (allCycleLinks source).map (fun link =>
      @List.idxOf (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq link.2 (rotatedOccurrenceVariables source)) =
    List.map id (List.range (occurrenceGroups source).flatten.length)
      at grouped
  rw [List.map_id] at grouped
  exact grouped

end CycleLinkGroupedTargetIndices
end PeriodicThreeSATThree
end LeanTrominoes

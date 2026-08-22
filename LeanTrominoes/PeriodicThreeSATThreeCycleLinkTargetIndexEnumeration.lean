/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkGroupedTargetIndices

/-! # Global target-index streams of grouped occurrence cycles -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedTargetIndices

theorem groupTargetIndices_shift (start size : Nat) :
    PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices start size =
      (PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices 0 size).map
        (fun index => start + index) := by
  unfold PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
  rw [List.map_map]
  apply List.map_congr_left
  intro position positionMember
  rw [List.mem_range] at positionMember
  cases position with
  | zero =>
      simp [PeriodicCNF.SourceCycleLinkTargetIndices.targetIndex]
      omega
  | succ position =>
      simp [PeriodicCNF.SourceCycleLinkTargetIndices.targetIndex]

theorem sourceTargetIndices_group
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (values : List (ThreeOccurrenceVariable Variable))
    (nodup : values.Nodup) :
    (cycleLinks values).map (fun link =>
        start + @List.idxOf _ instBEqOfDecidableEq link.1
          (rotatedGroup values)) =
      PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
        start values.length := by
  calc
    (cycleLinks values).map (fun link =>
        start + @List.idxOf _ instBEqOfDecidableEq link.1
          (rotatedGroup values)) =
      ((cycleLinks values).map (fun link =>
        @List.idxOf _ instBEqOfDecidableEq link.1
          (rotatedGroup values))).map (fun index => start + index) := by
        rw [List.map_map]
        rfl
    _ = (PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
          0 values.length).map (fun index => start + index) := by
      rw [sourceTargetIndices_group_zero values nodup]
    _ = PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
        start values.length := (groupTargetIndices_shift start _).symm

theorem targetIndices_group
    {Variable : Type*} [DecidableEq Variable]
    (start : Nat) (values : List (ThreeOccurrenceVariable Variable))
    (nodup : values.Nodup) :
    (cycleLinks values).map (fun link =>
        start + @List.idxOf _ instBEqOfDecidableEq link.2
          (rotatedGroup values)) =
      (List.range values.length).map (fun index => start + index) := by
  calc
    (cycleLinks values).map (fun link =>
        start + @List.idxOf _ instBEqOfDecidableEq link.2
          (rotatedGroup values)) =
      ((cycleLinks values).map (fun link =>
        @List.idxOf _ instBEqOfDecidableEq link.2
          (rotatedGroup values))).map (fun index => start + index) := by
        rw [List.map_map]
        rfl
    _ = (List.range values.length).map (fun index => start + index) := by
      rw [targetIndices_group_zero values nodup]

theorem groupedLinks_fst_mem_flatten
    {Variable : Type*}
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (link : ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)
    (member : link ∈ groupedLinks groups) :
    link.1 ∈ groups.flatten := by
  rw [groupedLinks, List.mem_flatMap] at member
  obtain ⟨group, groupMember, linkMember⟩ := member
  rw [List.mem_flatten]
  exact ⟨group, groupMember, cycleLink_fst_mem group link linkMember⟩

theorem groupedLinks_snd_mem_flatten
    {Variable : Type*}
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (link : ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)
    (member : link ∈ groupedLinks groups) :
    link.2 ∈ groups.flatten := by
  rw [groupedLinks, List.mem_flatMap] at member
  obtain ⟨group, groupMember, linkMember⟩ := member
  rw [List.mem_flatten]
  exact ⟨group, groupMember, cycleLink_snd_mem group link linkMember⟩

theorem sourceTargetIndices_grouped_aux
    {Variable : Type*} [DecidableEq Variable]
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (nodup : groups.flatten.Nodup) (start : Nat) :
    (groupedLinks groups).map (fun link =>
        start + @List.idxOf _ instBEqOfDecidableEq link.1
          (groupedRotated groups)) =
      PeriodicCNF.SourceCycleLinkTargetIndices.targetIndicesAux start
        (groups.map List.length) := by
  letI : BEq (ThreeOccurrenceVariable Variable) :=
    instBEqOfDecidableEq
  induction groups generalizing start with
  | nil => rfl
  | cons group groups induction =>
      have appendNodup : (group ++ groups.flatten).Nodup := by
        simpa using nodup
      have parts := List.nodup_append.mp appendNodup
      have groupNodup := parts.1
      have groupsNodup := parts.2.1
      have disjoint := parts.2.2
      have headEq :
          (cycleLinks group).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.1
                (rotatedGroup group ++ groupedRotated groups)) =
            PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
              start group.length := by
        calc
          (cycleLinks group).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.1
                (rotatedGroup group ++ groupedRotated groups)) =
              (cycleLinks group).map (fun link =>
                start + @List.idxOf _ instBEqOfDecidableEq link.1
                  (rotatedGroup group)) := by
            apply List.map_congr_left
            intro link linkMember
            have endpointMember := cycleLink_fst_mem group link linkMember
            have rotatedMember : link.1 ∈ rotatedGroup group :=
              (mem_rotatedGroup_iff link.1 group).2 endpointMember
            rw [List.idxOf_append_of_mem rotatedMember]
          _ = _ := sourceTargetIndices_group start group groupNodup
      have tailEq :
          (groupedLinks groups).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.1
                (rotatedGroup group ++ groupedRotated groups)) =
            PeriodicCNF.SourceCycleLinkTargetIndices.targetIndicesAux
              (start + group.length) (groups.map List.length) := by
        calc
          (groupedLinks groups).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.1
                (rotatedGroup group ++ groupedRotated groups)) =
              (groupedLinks groups).map (fun link =>
                (start + group.length) +
                  @List.idxOf _ instBEqOfDecidableEq link.1
                    (groupedRotated groups)) := by
            apply List.map_congr_left
            intro link linkMember
            have tailMember := groupedLinks_fst_mem_flatten
              groups link linkMember
            have notHead : link.1 ∉ rotatedGroup group := by
              intro headMember
              have headMember' :=
                (mem_rotatedGroup_iff link.1 group).1 headMember
              exact disjoint link.1 headMember' link.1 tailMember rfl
            rw [List.idxOf_append_of_notMem notHead,
              rotatedGroup_length]
            omega
          _ = _ := induction groupsNodup (start + group.length)
      simpa only [groupedLinks, groupedRotated, List.flatMap_cons,
        List.map_append, List.map_cons,
        PeriodicCNF.SourceCycleLinkTargetIndices.targetIndicesAux] using
          congrArg₂ (fun first second => first ++ second) headEq tailEq

theorem map_range_add_split (start first second : Nat) :
    (List.range (first + second)).map (fun index => start + index) =
      (List.range first).map (fun index => start + index) ++
        (List.range second).map
          (fun index => (start + first) + index) := by
  induction second with
  | zero => simp
  | succ second induction =>
      rw [Nat.add_succ, List.range_succ, List.map_append, induction,
        List.range_succ, List.map_append]
      simp [List.append_assoc]
      omega

theorem targetIndices_grouped_aux
    {Variable : Type*} [DecidableEq Variable]
    (groups : List (List (ThreeOccurrenceVariable Variable)))
    (nodup : groups.flatten.Nodup) (start : Nat) :
    (groupedLinks groups).map (fun link =>
        start + @List.idxOf _ instBEqOfDecidableEq link.2
          (groupedRotated groups)) =
      (List.range groups.flatten.length).map
        (fun index => start + index) := by
  letI : BEq (ThreeOccurrenceVariable Variable) :=
    instBEqOfDecidableEq
  induction groups generalizing start with
  | nil => rfl
  | cons group groups induction =>
      have appendNodup : (group ++ groups.flatten).Nodup := by
        simpa using nodup
      have parts := List.nodup_append.mp appendNodup
      have groupNodup := parts.1
      have groupsNodup := parts.2.1
      have disjoint := parts.2.2
      have headEq :
          (cycleLinks group).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.2
                (rotatedGroup group ++ groupedRotated groups)) =
            (List.range group.length).map
              (fun index => start + index) := by
        calc
          (cycleLinks group).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.2
                (rotatedGroup group ++ groupedRotated groups)) =
              (cycleLinks group).map (fun link =>
                start + @List.idxOf _ instBEqOfDecidableEq link.2
                  (rotatedGroup group)) := by
            apply List.map_congr_left
            intro link linkMember
            have endpointMember := cycleLink_snd_mem group link linkMember
            have rotatedMember : link.2 ∈ rotatedGroup group :=
              (mem_rotatedGroup_iff link.2 group).2 endpointMember
            rw [List.idxOf_append_of_mem rotatedMember]
          _ = _ := targetIndices_group start group groupNodup
      have tailEq :
          (groupedLinks groups).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.2
                (rotatedGroup group ++ groupedRotated groups)) =
            (List.range groups.flatten.length).map
              (fun index => (start + group.length) + index) := by
        calc
          (groupedLinks groups).map (fun link =>
              start + @List.idxOf _ instBEqOfDecidableEq link.2
                (rotatedGroup group ++ groupedRotated groups)) =
              (groupedLinks groups).map (fun link =>
                (start + group.length) +
                  @List.idxOf _ instBEqOfDecidableEq link.2
                    (groupedRotated groups)) := by
            apply List.map_congr_left
            intro link linkMember
            have tailMember := groupedLinks_snd_mem_flatten
              groups link linkMember
            have notHead : link.2 ∉ rotatedGroup group := by
              intro headMember
              have headMember' :=
                (mem_rotatedGroup_iff link.2 group).1 headMember
              exact disjoint link.2 headMember' link.2 tailMember rfl
            rw [List.idxOf_append_of_notMem notHead,
              rotatedGroup_length]
            omega
          _ = _ := induction groupsNodup (start + group.length)
      have joined := congrArg₂ (fun first second => first ++ second)
        headEq tailEq
      simpa only [groupedLinks, groupedRotated, List.flatMap_cons,
        List.map_append, List.flatten_cons, List.length_append,
        map_range_add_split] using joined

end CycleLinkGroupedTargetIndices
end PeriodicThreeSATThree
end LeanTrominoes

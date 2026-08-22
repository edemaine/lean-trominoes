/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkPositionTags

/-! # Cycle-link boundary-tag rank semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

/-- Source-incidence target ranks in positional form. -/
def sourceRanks (groupSize : Nat) : List Nat :=
  (List.range groupSize).map fun position =>
    if position = 0 then 1 else 2

/-- Target-incidence target ranks in positional form. -/
def targetRanks (groupSize : Nat) : List Nat :=
  (List.range groupSize).map fun position =>
    if position + 1 = groupSize then 2 else 1

@[simp] theorem sourceRanks_succ (count : Nat) :
    sourceRanks (count + 1) = 1 :: List.replicate count 2 := by
  unfold sourceRanks
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, ite_true]
  congr 1
  calc
    (List.range count).map
          ((fun position => if position = 0 then 1 else 2) ∘ Nat.succ) =
        (List.range count).map (fun _ => 2) := by
      apply List.map_congr_left
      intro position _
      simp
    _ = List.replicate count 2 := by simp [List.map_const']

@[simp] theorem targetRanks_succ (count : Nat) :
    targetRanks (count + 1) = List.replicate count 1 ++ [2] := by
  unfold targetRanks
  rw [List.range_succ]
  simp only [List.map_append, List.map_singleton]
  have prefixEq :
      (List.range count).map
          (fun position => if position + 1 = count + 1 then 2 else 1) =
        List.replicate count 1 := by
    calc
      (List.range count).map
            (fun position =>
              if position + 1 = count + 1 then 2 else 1) =
          (List.range count).map (fun _ => 1) := by
        apply List.map_congr_left
        intro position positionMem
        rw [List.mem_range] at positionMem
        simp only [ite_eq_right_iff]
        omega
      _ = List.replicate count 1 := by simp [List.map_const']
  rw [prefixEq]
  simp

/-- Boundary tags encode exactly the positional source target-port ranks. -/
theorem map_sourceTargetPortRank_groupTags (groupSize : Nat) :
    (groupTags groupSize).map sourceTargetPortRank = sourceRanks groupSize := by
  cases groupSize with
  | zero => rfl
  | succ count =>
      rw [map_sourceTargetPortRank_groupTags_succ, sourceRanks_succ]

/-- Boundary tags encode exactly the positional target target-port ranks. -/
theorem map_targetTargetPortRank_groupTags (groupSize : Nat) :
    (groupTags groupSize).map targetTargetPortRank = targetRanks groupSize := by
  cases groupSize with
  | zero => rfl
  | succ count =>
      rw [map_targetTargetPortRank_groupTags_succ, targetRanks_succ]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

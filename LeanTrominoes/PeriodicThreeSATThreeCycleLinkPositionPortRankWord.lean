/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkGroupedPortRankEnumeration

/-! # Positional interpretation of cycle-link port ranks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

def positionRankBlock (groupSize position : Nat) : List Nat :=
  [if position = 0 then 1 else 2,
    if position + 1 = groupSize then 2 else 1]

def positionalRankWord (groupSize : Nat) : List Nat :=
  (List.range groupSize).flatMap (positionRankBlock groupSize)

theorem positionalRankWord_add_two (count : Nat) :
    positionalRankWord (count + 2) = groupRankWord (count + 2) := by
  have rangeEq : List.range (count + 2) =
      0 :: (List.range count).map Nat.succ ++ [count + 1] := by
    calc
      List.range (count + 2) =
          List.range (count + 1) ++ [count + 1] := by
        rw [show count + 2 = (count + 1) + 1 by omega,
          List.range_succ]
      _ = (0 :: (List.range count).map Nat.succ) ++ [count + 1] := by
        rw [List.range_succ_eq_map]
      _ = 0 :: (List.range count).map Nat.succ ++ [count + 1] := rfl
  have firstBlock : positionRankBlock (count + 2) 0 = [1, 1] := by
    simp [positionRankBlock]
  have lastBlock :
      positionRankBlock (count + 2) (count + 1) = [2, 2] := by
    simp [positionRankBlock]
  have middleBlocks :
      (List.range count).flatMap (fun position =>
          positionRankBlock (count + 2) position.succ) =
        repeatPair 2 1 count := by
    calc
      (List.range count).flatMap (fun position =>
          positionRankBlock (count + 2) position.succ) =
          (List.range count).flatMap (fun _ => [2, 1]) := by
        apply List.flatMap_congr
        intro position positionMember
        rw [List.mem_range] at positionMember
        simp [positionRankBlock]
        omega
      _ = repeatPair 2 1 (List.range count).length :=
        flatMap_const_pair (List.range count) 2 1
      _ = repeatPair 2 1 count := by simp
  unfold positionalRankWord
  rw [rangeEq]
  simp only [List.flatMap_cons, List.flatMap_append,
    List.flatMap_map, List.flatMap_nil, List.append_nil]
  rw [firstBlock, middleBlocks, lastBlock]
  rfl

theorem positionalRankWord_eq_groupRankWord (groupSize : Nat) :
    positionalRankWord groupSize = groupRankWord groupSize := by
  cases groupSize with
  | zero => rfl
  | succ count =>
      cases count with
      | zero => rfl
      | succ count =>
          exact positionalRankWord_add_two count

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes

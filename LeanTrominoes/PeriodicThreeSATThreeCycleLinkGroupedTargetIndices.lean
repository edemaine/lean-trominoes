/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListSumFiberPartition
import LeanTrominoes.PeriodicCNFSourceCycleLinkTargetIndices
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkEndpoints
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkZip

/-! # Target indices in grouped occurrence cycles -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedTargetIndices

def rotatedGroup {Value : Type*} (values : List Value) : List Value :=
  values.tail ++ values.take 1

def groupedLinks {Variable : Type*}
    (groups : List (List (ThreeOccurrenceVariable Variable))) :
    List (ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable) :=
  groups.flatMap cycleLinks

def groupedRotated {Value : Type*} (groups : List (List Value)) :
    List Value :=
  groups.flatMap rotatedGroup

@[simp] theorem rotatedGroup_length {Value : Type*}
    (values : List Value) :
    (rotatedGroup values).length = values.length := by
  cases values <;> simp [rotatedGroup]

@[simp] theorem mem_rotatedGroup_iff {Value : Type*}
    (value : Value) (values : List Value) :
    value ∈ rotatedGroup values ↔ value ∈ values := by
  cases values <;> simp [rotatedGroup, or_comm]

theorem rotatedGroup_nodup {Value : Type*} (values : List Value)
    (nodup : values.Nodup) :
    (rotatedGroup values).Nodup := by
  cases values with
  | nil => simp [rotatedGroup]
  | cons head tail =>
      have perm : (tail ++ [head]).Perm (head :: tail) := by
        change (tail ++ [head]).Perm ([head] ++ tail)
        exact List.perm_append_comm
      exact perm.nodup_iff.mpr nodup

@[simp] theorem map_fst_cycleLinks {Variable : Type*}
    (values : List (ThreeOccurrenceVariable Variable)) :
    (cycleLinks values).map Prod.fst = values := by
  rw [cycleLinks_eq_zip]
  change (List.zip values (rotatedGroup values)).map Prod.fst = values
  exact List.map_fst_zip (by rw [rotatedGroup_length])

@[simp] theorem map_snd_cycleLinks {Variable : Type*}
    (values : List (ThreeOccurrenceVariable Variable)) :
    (cycleLinks values).map Prod.snd = rotatedGroup values := by
  rw [cycleLinks_eq_zip]
  change (List.zip values (rotatedGroup values)).map Prod.snd =
    rotatedGroup values
  exact List.map_snd_zip (by rw [rotatedGroup_length])

theorem sourceTargetIndices_group_zero
    {Variable : Type*} [DecidableEq Variable]
    (values : List (ThreeOccurrenceVariable Variable))
    (nodup : values.Nodup) :
    (cycleLinks values).map (fun link =>
        @List.idxOf _ instBEqOfDecidableEq link.1
          (rotatedGroup values)) =
      PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
        0 values.length := by
  letI : BEq (ThreeOccurrenceVariable Variable) :=
    instBEqOfDecidableEq
  calc
    (cycleLinks values).map (fun link =>
        @List.idxOf _ instBEqOfDecidableEq link.1
          (rotatedGroup values)) =
        ((cycleLinks values).map Prod.fst).map
          (fun value => @List.idxOf _ instBEqOfDecidableEq value
            (rotatedGroup values)) := by
      rw [List.map_map]
      rfl
    _ = values.map (fun value =>
        @List.idxOf _ instBEqOfDecidableEq value
          (rotatedGroup values)) := by
      rw [map_fst_cycleLinks]
    _ = PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices
        0 values.length := by
      cases values with
      | nil => rfl
      | cons head tail =>
          have headNotTail := (List.nodup_cons.mp nodup).1
          have tailNodup := (List.nodup_cons.mp nodup).2
          have tailIndices :
              tail.map (fun value =>
                @List.idxOf _ instBEqOfDecidableEq value
                  (tail ++ [head])) =
                List.range tail.length := by
            calc
              tail.map (fun value =>
                  @List.idxOf _ instBEqOfDecidableEq value
                    (tail ++ [head])) =
                  tail.map (fun value =>
                    @List.idxOf _ instBEqOfDecidableEq value tail) := by
                apply List.map_congr_left
                intro value valueMember
                rw [List.idxOf_append_of_mem valueMember]
              _ = List.range tail.length :=
                List.map_idxOf_self_eq_range tail tailNodup
          simp only [List.length_cons]
          rw [PeriodicCNF.SourceCycleLinkTargetIndices.groupTargetIndices_succ]
          simp only [rotatedGroup, List.map_cons, List.tail_cons,
            List.take_succ_cons, List.take_zero]
          rw [List.idxOf_append_of_notMem headNotTail, tailIndices]
          simp

theorem targetIndices_group_zero
    {Variable : Type*} [DecidableEq Variable]
    (values : List (ThreeOccurrenceVariable Variable))
    (nodup : values.Nodup) :
    (cycleLinks values).map (fun link =>
        @List.idxOf _ instBEqOfDecidableEq link.2
          (rotatedGroup values)) =
      List.range values.length := by
  letI : BEq (ThreeOccurrenceVariable Variable) :=
    instBEqOfDecidableEq
  calc
    (cycleLinks values).map (fun link =>
        @List.idxOf _ instBEqOfDecidableEq link.2
          (rotatedGroup values)) =
        ((cycleLinks values).map Prod.snd).map
          (fun value => @List.idxOf _ instBEqOfDecidableEq value
            (rotatedGroup values)) := by
      rw [List.map_map]
      rfl
    _ = (rotatedGroup values).map
        (fun value => @List.idxOf _ instBEqOfDecidableEq value
          (rotatedGroup values)) := by
      rw [map_snd_cycleLinks]
    _ = List.range (rotatedGroup values).length :=
      List.map_idxOf_self_eq_range _
        (rotatedGroup_nodup values nodup)
    _ = List.range values.length := by rw [rotatedGroup_length]

end CycleLinkGroupedTargetIndices
end PeriodicThreeSATThree
end LeanTrominoes

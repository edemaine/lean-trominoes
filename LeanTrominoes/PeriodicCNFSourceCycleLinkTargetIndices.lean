/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterData

/-! # Source target indices for cycle-link routes -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTargetIndices

/-- The variable-vertex index of the negative endpoint at one local link
position.  The first occurrence wraps to the end of its atom block. -/
def targetIndex (blockStart groupSize position : Nat) : Nat :=
  if position = 0 then blockStart + groupSize - 1
  else blockStart + position - 1

@[simp] theorem targetIndex_zero (blockStart groupSize : Nat) :
    targetIndex blockStart groupSize 0 =
      blockStart + groupSize - 1 := by
  simp [targetIndex]

@[simp] theorem targetIndex_succ (blockStart groupSize position : Nat) :
    targetIndex blockStart groupSize (position + 1) =
      blockStart + position := by
  simp [targetIndex]

/-- One atom block's targets, in cycle-link order. -/
def groupTargetIndices (blockStart groupSize : Nat) : List Nat :=
  (List.range groupSize).map (targetIndex blockStart groupSize)

@[simp] theorem groupTargetIndices_length (blockStart groupSize : Nat) :
    (groupTargetIndices blockStart groupSize).length = groupSize := by
  simp [groupTargetIndices]

/-- A positive block emits its last index first, followed by all preceding
indices in increasing order. -/
theorem groupTargetIndices_succ (blockStart count : Nat) :
    groupTargetIndices blockStart (count + 1) =
      (blockStart + count) ::
        (List.range count).map (fun position => blockStart + position) := by
  unfold groupTargetIndices
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, targetIndex_zero]
  congr 1

/-- Successive atom blocks while carrying the next global block start. -/
def targetIndicesAux : Nat → List Nat → List Nat
  | _, [] => []
  | blockStart, groupSize :: groupSizes =>
      groupTargetIndices blockStart groupSize ++
        targetIndicesAux (blockStart + groupSize) groupSizes

/-- Complete negative-source target stream for all cycle links. -/
def targetIndices (groupSizes : List Nat) : List Nat :=
  targetIndicesAux 0 groupSizes

@[simp] theorem targetIndicesAux_length
    (blockStart : Nat) (groupSizes : List Nat) :
    (targetIndicesAux blockStart groupSizes).length = groupSizes.sum := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      simp [targetIndicesAux, induction]

@[simp] theorem targetIndices_length (groupSizes : List Nat) :
    (targetIndices groupSizes).length = groupSizes.sum := by
  simp [targetIndices]

/-- The semantic route emitter's fifth source field is exactly the target
stream entry defined above. -/
theorem sourceFields_targetIndex
    (input : SourceCycleLinkRouteEmitter.Input)
    (blockStart groupSize position : Nat) :
    (SourceCycleLinkRouteEmitter.sourceFields input groupSize
      (blockStart + position) position)[4]? =
        some (targetIndex blockStart groupSize position) := by
  cases position <;> simp [SourceCycleLinkRouteEmitter.sourceFields,
    targetIndex]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTargetIndices

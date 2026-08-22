/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Finite boundary tags for source cycle-link groups -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

/-- Boundary classification of one link position within its atom group. -/
inductive Tag
  | singleton
  | first
  | middle
  | last
  deriving DecidableEq, Fintype, Inhabited

/-- Tags contributed by one unary group size. -/
def groupTags : Nat → List Tag
  | 0 => []
  | 1 => [.singleton]
  | count + 2 => .first :: List.replicate count .middle ++ [.last]

/-- Complete group-boundary tag stream. -/
def tags (groupSizes : List Nat) : List Tag :=
  groupSizes.flatMap groupTags

/-- Target-port rank of the negative-source incidence at this link. -/
def sourceTargetPortRank : Tag → Nat
  | .singleton | .first => 1
  | .middle | .last => 2

/-- Target-port rank of the positive-target incidence at this link. -/
def targetTargetPortRank : Tag → Nat
  | .singleton | .last => 2
  | .first | .middle => 1

@[simp] theorem groupTags_length (groupSize : Nat) :
    (groupTags groupSize).length = groupSize := by
  cases groupSize with
  | zero => rfl
  | succ groupSize =>
      cases groupSize with
      | zero => rfl
      | succ count => simp [groupTags]

@[simp] theorem tags_length (groupSizes : List Nat) :
    (tags groupSizes).length = groupSizes.sum := by
  simp [tags]

/-- In a positive group, only its first source incidence has rank one. -/
@[simp] theorem map_sourceTargetPortRank_groupTags_succ (count : Nat) :
    (groupTags (count + 1)).map sourceTargetPortRank =
      1 :: List.replicate count 2 := by
  cases count with
  | zero => rfl
  | succ count =>
      simp only [groupTags, List.map_cons, List.map_append,
        List.map_replicate, sourceTargetPortRank, List.map_nil,
        List.cons_append]
      rw [List.replicate_succ']

/-- In a positive group, only its last target incidence has rank two. -/
@[simp] theorem map_targetTargetPortRank_groupTags_succ (count : Nat) :
    (groupTags (count + 1)).map targetTargetPortRank =
      List.replicate count 1 ++ [2] := by
  cases count with
  | zero => rfl
  | succ count =>
      simp only [groupTags, List.map_cons, List.map_append,
        List.map_replicate, targetTargetPortRank, List.map_nil,
        List.cons_append]
      rw [List.replicate_succ, List.cons_append]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

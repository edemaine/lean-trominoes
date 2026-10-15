/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorData
import LeanTrominoes.Common.Geometry.GridSegmentStraightRayKeys
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

/-! # Assigning the rectangle profile from distinct rational incidence rays -/
namespace LeanTrominoes

def StraightRayKey.clockwiseCode : StraightRayKey → Nat ×ₗ ℚ
  | .right slope => toLex (0,-slope)
  | .down => toLex (1,0)
  | .left slope => toLex (2,-slope)
  | .up => toLex (3,0)

theorem StraightRayKey.clockwiseCode_injective : Function.Injective StraightRayKey.clockwiseCode := by
  intro first second equal
  cases first <;> cases second <;> simp_all [clockwiseCode]

def StraightRayKey.isRight : StraightRayKey → Bool
  | .right _ => true
  | _ => false

def StraightRayKey.isLeft : StraightRayKey → Bool
  | .left _ => true
  | _ => false

theorem straightRayKey_count_partition (keys : List StraightRayKey) :
    keys.countP StraightRayKey.isRight + keys.countP StraightRayKey.isLeft +
      keys.countP (fun key => decide (key = .up)) + keys.countP (fun key => decide (key = .down)) = keys.length := by
  induction keys with
  | nil => simp
  | cons head tail ih =>
    cases head <;> simp [StraightRayKey.isRight,StraightRayKey.isLeft,List.countP_cons] <;> omega

theorem straightRayKey_singleton_count {keys : List StraightRayKey} (nodup : keys.Nodup) (key : StraightRayKey) :
    keys.countP (fun candidate => decide (candidate = key)) = if key ∈ keys then 1 else 0 := by
  induction keys with
  | nil => simp
  | cons head tail ih =>
    have tailNodup := List.nodup_cons.mp nodup
    by_cases equal : head = key
    · subst head
      have zero : tail.countP (fun candidate => decide (candidate = key)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro candidate member
        simp only [decide_eq_true_eq]
        intro equal
        exact tailNodup.1 (equal ▸ member)
      simp [zero,List.countP_cons]
    · simp [equal,Ne.symm equal,ih tailNodup.2]

namespace OrthogonalDrawingRefinement

def anchorProfileOfKeys (keys : List StraightRayKey) : AnchorProfile where
  leftCount := ⟨min (keys.countP StraightRayKey.isLeft) 4,by omega⟩
  rightCount := ⟨min (keys.countP StraightRayKey.isRight) 4,by omega⟩
  top := decide (.up ∈ keys)
  bottom := decide (.down ∈ keys)

theorem anchorProfileOfKeys_degree {keys : List StraightRayKey} (nodup : keys.Nodup) (bound : keys.length ≤ 4) :
    (anchorProfileOfKeys keys).degree = keys.length := by
  have leftBound := List.countP_le_length (p := StraightRayKey.isLeft) (l := keys)
  have rightBound := List.countP_le_length (p := StraightRayKey.isRight) (l := keys)
  have partition := straightRayKey_count_partition keys
  have topCount := straightRayKey_singleton_count nodup .up
  have bottomCount := straightRayKey_singleton_count nodup .down
  simp only [anchorProfileOfKeys,AnchorProfile.degree,decide_eq_true_eq,
    Nat.min_eq_left (by omega : keys.countP StraightRayKey.isLeft ≤ 4),
    Nat.min_eq_left (by omega : keys.countP StraightRayKey.isRight ≤ 4)]
  omega

def clockwiseKeys (keys : List StraightRayKey) : List StraightRayKey :=
  keys.mergeSort (fun first second => decide (first.clockwiseCode ≤ second.clockwiseCode))

theorem clockwiseKeys_perm (keys : List StraightRayKey) : (clockwiseKeys keys).Perm keys :=
  List.mergeSort_perm _ _

theorem clockwiseKeys_nodup {keys : List StraightRayKey} (nodup : keys.Nodup) : (clockwiseKeys keys).Nodup :=
  (clockwiseKeys_perm keys).nodup_iff.mpr nodup

theorem clockwiseKeys_ordered (keys : List StraightRayKey) :
    (clockwiseKeys keys).Pairwise (fun first second => first.clockwiseCode ≤ second.clockwiseCode) := by
  have ordered := List.pairwise_mergeSort
    (le := fun first second : StraightRayKey => decide (first.clockwiseCode ≤ second.clockwiseCode))
    (by intro first second third h1 h2; simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (by intro first second; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _) keys
  simpa [clockwiseKeys] using ordered

theorem clockwiseKeys_strict {keys : List StraightRayKey} (nodup : keys.Nodup) :
    (clockwiseKeys keys).Pairwise (fun first second => first.clockwiseCode < second.clockwiseCode) := by
  have ordered := clockwiseKeys_ordered keys
  have distinct := clockwiseKeys_nodup nodup
  apply (ordered.and distinct).imp
  intro first second both
  exact lt_of_le_of_ne both.1 (fun equal => both.2 (StraightRayKey.clockwiseCode_injective equal))

end OrthogonalDrawingRefinement
end LeanTrominoes

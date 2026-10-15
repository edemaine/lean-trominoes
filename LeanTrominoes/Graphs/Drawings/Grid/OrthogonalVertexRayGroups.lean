/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorGroups
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorAssignment

/-! # Clockwise rational rays match the four boundary-anchor groups -/
namespace LeanTrominoes

def StraightRayKey.group : StraightRayKey → Fin 4
  | .right _ => 0
  | .down => 1
  | .left _ => 2
  | .up => 3

theorem StraightRayKey.group_val (key : StraightRayKey) : key.group.val = (ofLex key.clockwiseCode).1 := by
  cases key <;> rfl

theorem StraightRayKey.group_monotone {first second : StraightRayKey} (ordered : first.clockwiseCode ≤ second.clockwiseCode) :
    first.group ≤ second.group := by
  change first.group.val ≤ second.group.val
  rw [group_val,group_val]
  exact Prod.Lex.monotone_fst _ _ ordered

theorem StraightRayKey.group_eq_up (key : StraightRayKey) : key.group = 3 ↔ key = .up := by
  cases key <;> simp [group]

theorem StraightRayKey.group_eq_down (key : StraightRayKey) : key.group = 1 ↔ key = .down := by
  cases key <;> simp [group]

namespace OrthogonalDrawingRefinement

theorem anchorProfileOfGroups_eq_keys (keys : List StraightRayKey) :
    anchorProfileOfGroups (keys.map StraightRayKey.group) = anchorProfileOfKeys keys := by
  have leftPredicate : (fun key : StraightRayKey => decide (key.group = 2)) = StraightRayKey.isLeft := by
    funext key
    cases key <;> rfl
  have rightPredicate : (fun key : StraightRayKey => decide (key.group = 0)) = StraightRayKey.isRight := by
    funext key
    cases key <;> rfl
  have upMember : (3 : Fin 4) ∈ keys.map StraightRayKey.group ↔ StraightRayKey.up ∈ keys := by
    simp [List.mem_map,StraightRayKey.group_eq_up]
  have downMember : (1 : Fin 4) ∈ keys.map StraightRayKey.group ↔ StraightRayKey.down ∈ keys := by
    simp [List.mem_map,StraightRayKey.group_eq_down]
  simp only [anchorProfileOfGroups,anchorProfileOfKeys,List.countP_map,Function.comp_def,leftPredicate,rightPredicate,upMember,downMember]

theorem rayGroups_vertical_count {keys : List StraightRayKey} (nodup : keys.Nodup) :
    (keys.map StraightRayKey.group).countP (fun group => decide (group = 1)) ≤ 1 ∧
      (keys.map StraightRayKey.group).countP (fun group => decide (group = 3)) ≤ 1 := by
  have downPredicate : (fun key : StraightRayKey => decide (key.group = 1)) = (fun key => decide (key = .down)) := by
    funext key
    simp only [StraightRayKey.group_eq_down]
  have upPredicate : (fun key : StraightRayKey => decide (key.group = 3)) = (fun key => decide (key = .up)) := by
    funext key
    simp only [StraightRayKey.group_eq_up]
  simp only [List.countP_map,Function.comp_def,downPredicate,upPredicate,straightRayKey_singleton_count nodup]
  constructor <;> split <;> omega

theorem rayGroups_eq_anchorGroups {keys : List StraightRayKey} (nodup : keys.Nodup) (bound : keys.length ≤ 4)
    (ordered : keys.Pairwise (fun first second => first.clockwiseCode ≤ second.clockwiseCode)) :
    (anchorProfileOfKeys keys).anchorGroups = keys.map StraightRayKey.group := by
  have groupOrder := ordered.map StraightRayKey.group (fun _ _ ordered => StraightRayKey.group_monotone ordered)
  have counts := rayGroups_vertical_count nodup
  rw [← anchorProfileOfGroups_eq_keys]
  exact sorted_groups_eq_anchorGroups (by simpa using bound) groupOrder counts.1 counts.2

end OrthogonalDrawingRefinement
end LeanTrominoes

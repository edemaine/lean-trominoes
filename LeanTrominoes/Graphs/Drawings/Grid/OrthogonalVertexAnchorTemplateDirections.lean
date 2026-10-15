/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorTemplates

/-! # Rectangle connectors retain the clockwise order of their boundary anchors -/
namespace LeanTrominoes.OrthogonalDrawingRefinement

def clockwiseDirectionIndex : AxisDirection → Nat
  | .east => 0
  | .south => 1
  | .west => 2
  | .north => 3
  | .invalid => 4

def AnchorProfile.initialDirections (profile : AnchorProfile) : List AxisDirection :=
  ((List.finRange 4).filter (fun index => decide (index.val < profile.degree))).map
    (fun index => AxisDirection.polylineFirstDirection (rectangleTemplate profile index))

def ClockwiseDirections (directions : List AxisDirection) : Prop :=
  ∃ rotation : Fin 4,
    (directions.map (fun direction => (clockwiseDirectionIndex direction+rotation.val)%4)).Pairwise (· < ·)

instance (directions : List AxisDirection) : Decidable (ClockwiseDirections directions) := by
  unfold ClockwiseDirections
  infer_instance

theorem rectangleTemplate_firstDirection_genuine (profile : AnchorProfile) (index : Fin 4) :
    (AxisDirection.polylineFirstDirection (rectangleTemplate profile index)).IsGenuine := by
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem AnchorProfile.initialDirections_nodup (profile : AnchorProfile) (degree : profile.degree ≤ 4) :
    profile.initialDirections.Nodup := by
  revert degree
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> decide +kernel

theorem AnchorProfile.initialDirections_clockwise (profile : AnchorProfile) (degree : profile.degree ≤ 4) :
    ClockwiseDirections profile.initialDirections := by
  revert degree
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> decide +kernel

end LeanTrominoes.OrthogonalDrawingRefinement

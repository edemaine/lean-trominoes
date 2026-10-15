/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEndpoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceParameterPoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingPieceWindow

/-! # Fan anchors have matching old and new cut coordinates -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem endpointPort_nonvertical_anchor_x {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) (target : Bool) :
    (portBoundaryAnchor graph drawing (endpointPort tagged target)).1 =
      if (if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 then target else !target) then -5 else 5 := by
  have anchor := portBoundaryAnchor_x (distinctPortRayKeys_of_planar_straight planar straight) degree (endpointPort_mem graph member target)
  have startEq : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 = (drawing.straightSegment tagged.2).start.1 := by
    simp [liftedStraightSegment,GridSegment.translate,periodTranslation,Cell.scale,Cell.add]
  have finishEq : (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 = (drawing.straightSegment tagged.2).finish.1 := by
    simp [liftedStraightSegment,GridSegment.translate,periodTranslation,Cell.scale,Cell.add]
  rw [startEq,finishEq] at nonvertical ⊢
  cases target <;> rcases lt_or_gt_of_ne nonvertical with direction | direction
  all_goals simpa [endpointPort,portRayKey,sourcePort,targetPort,GridSegment.straightRayKey,GridSegment.reverse,
    direction,not_lt_of_gt direction,StraightRayKey.group,groupBoundaryX] using anchor

set_option maxRecDepth 2048 in
theorem fanEdgePiece_outer_endpoint_data {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) (target : Bool) :
    let line := if target then (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 else (drawing.liftedStraightSegment tagged.2 (0,0)).start.1
    let right := if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 then target else !target
    (if target then (targetEdgePiece graph drawing tagged).route.head? else (sourceEdgePiece graph drawing tagged).route.getLast?).map Prod.fst =
      some ((paddedRefinementFactor drawing.gridSize : Int)*line+(if right then -5 else 5)*crossingBound drawing.gridSize) ∧
    ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter
      (if target then (targetEdgePiece graph drawing tagged).start else (sourceEdgePiece graph drawing tagged).finish)).1 =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
  have anchor := endpointPort_nonvertical_anchor_x planar degree straight member nonvertical target
  have sourceX := sourceEdgePiece_finish_original_x graph drawing tagged nonvertical
  have targetX := targetEdgePiece_start_original_x graph drawing tagged nonvertical
  dsimp only
  constructor
  · cases target
    · rw [sourceEdgePiece_last planar degree straight member]
      simp only [Option.map_some,Cell.add,Cell.scale,endpointPort,Bool.false_eq_true,if_false] at anchor ⊢
      rw [anchor,liftedStraightSegment_start planar.1.1 member]
      simp [Cell.add,Cell.scale,periodTranslation,mul_comm]
    · rw [targetEdgePiece_head planar degree straight member]
      simp only [Option.map_some,Cell.add,Cell.scale,endpointPort,if_true] at anchor ⊢
      rw [anchor,liftedStraightSegment_finish planar.1.1 member]
      simp only [Cell.add,Cell.scale,periodTranslation,zero_add]
      simp only [paddedGridSize,Nat.cast_mul]
      apply congrArg some
      ring
  · cases target <;> by_cases forward : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
    · simpa [forward] using sourceX
    · simpa [forward] using sourceX
    · simpa [forward] using targetX
    · simpa [forward] using targetX

end LeanTrominoes.PeriodicGridDrawing

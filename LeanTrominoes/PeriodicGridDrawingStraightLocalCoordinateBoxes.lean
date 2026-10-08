/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentLocalCellContact
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow
import LeanTrominoes.GridSegmentRealIntersection

/-! # A straight edge stays inside the open box of its endpoint period cells -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem straightSegment_rational_local_coordinate_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {point : ℚ × ℚ} (contains : (drawing.liftedStraightSegment tagged.2 (0,0)).RealContains (point.1,point.2))
    (xShift yShift : ℚ) (xShiftBounds : 0 ≤ xShift ∧ xShift < 1) (yShiftBounds : 0 ≤ yShift ∧ yShift < 1) :
    ((drawing.gridSize : ℚ)*(min 0 tagged.1.offset.1 : Int) < point.1+xShift ∧
      point.1+xShift < (drawing.gridSize : ℚ)*((max 0 tagged.1.offset.1 : Int)+1)) ∧
    ((drawing.gridSize : ℚ)*(min 0 tagged.1.offset.2 : Int) < point.2+yShift ∧
      point.2+yShift < (drawing.gridSize : ℚ)*((max 0 tagged.1.offset.2 : Int)+1)) := by
  have sourceEq := liftedStraightSegment_start compatible member (0,0)
  have targetEq := liftedStraightSegment_finish compatible member (0,0)
  have sourceBounds := compatible.2.2.2.2.1 _
    (compatible.vertexPosition_mem (port_vertex_mem compatible.1 (sourcePort_mem_allPorts graph member)))
  have targetBounds := compatible.2.2.2.2.1 _
    (compatible.vertexPosition_mem (port_vertex_mem compatible.1 (targetPort_mem_allPorts graph member)))
  change (0 < (drawing.vertexPosition graph tagged.1.source).1 ∧ _ ∧ _ ∧ _) at sourceBounds
  change (0 < (drawing.vertexPosition graph tagged.1.target).1 ∧ _ ∧ _ ∧ _) at targetBounds
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have box := GridSegment.realBoxContains_of_realContains contains
  have xBox : (min (drawing.vertexPosition graph tagged.1.source).1
      ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*tagged.1.offset.1) : Int) ≤ point.1 ∧
      point.1 ≤ (max (drawing.vertexPosition graph tagged.1.source).1
        ((drawing.vertexPosition graph tagged.1.target).1+(drawing.gridSize : Int)*tagged.1.offset.1) : Int) := by
    have bounds := And.intro box.1 box.2.1
    simp only [sourceEq,targetEq,Cell.add,periodTranslation,Cell.scale,mul_zero,add_zero,zero_add] at bounds
    exact_mod_cast bounds
  have yBox : (min (drawing.vertexPosition graph tagged.1.source).2
      ((drawing.vertexPosition graph tagged.1.target).2+(drawing.gridSize : Int)*tagged.1.offset.2) : Int) ≤ point.2 ∧
      point.2 ≤ (max (drawing.vertexPosition graph tagged.1.source).2
        ((drawing.vertexPosition graph tagged.1.target).2+(drawing.gridSize : Int)*tagged.1.offset.2) : Int) := by
    have bounds := box.2.2
    simp only [sourceEq,targetEq,Cell.add,periodTranslation,Cell.scale,mul_zero,add_zero,zero_add] at bounds
    exact_mod_cast bounds
  exact ⟨GridSegment.local_coordinate_shifted_open_box positive ⟨sourceBounds.1,sourceBounds.2.1⟩
    ⟨targetBounds.1,targetBounds.2.1⟩ xShiftBounds xBox,
    GridSegment.local_coordinate_shifted_open_box positive ⟨sourceBounds.2.2.1,sourceBounds.2.2.2⟩
    ⟨targetBounds.2.2.1,targetBounds.2.2.2⟩ yShiftBounds yBox⟩

end LeanTrominoes.PeriodicGridDrawing

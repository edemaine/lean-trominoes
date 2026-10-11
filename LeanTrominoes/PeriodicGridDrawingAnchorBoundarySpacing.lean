/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingAnchorBoundaryOrder

/-! # Two-unit spacing of assigned horizontal boundary ports

Horizontal-side anchor ordinates are odd. The existing strict port order
therefore supplies the two-unit gap used by digital core separation.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

theorem AnchorProfile.horizontal_anchor_odd (profile : AnchorProfile) (index : Fin 4)
    (degree : profile.degree ≤ 4) (valid : index.val < profile.degree)
    (horizontal : profile.anchorGroups[index.val]? = some 0 ∨ profile.anchorGroups[index.val]? = some 2) :
    (profile.anchors[index.val]?.getD (0,0)).2 % 2 = 1 := by
  revert degree valid horizontal
  rcases profile with ⟨left,right,top,bottom⟩
  fin_cases left <;> fin_cases right <;> cases top <;> cases bottom <;> fin_cases index <;> decide +kernel

theorem portBoundaryAnchor_horizontal_odd {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph)
    (horizontal : (drawing.portRayKey port).group = 0 ∨ (drawing.portRayKey port).group = 2) :
    (portBoundaryAnchor graph drawing port).2 % 2 = 1 := by
  apply AnchorProfile.horizontal_anchor_odd _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree member)
  rw [incidenceAnchor_group distinct degree member]
  simpa using horizontal

theorem right_portBoundaryAnchor_gap {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) {firstSlope secondSlope : ℚ}
    (firstKey : drawing.portRayKey first = .right firstSlope) (secondKey : drawing.portRayKey second = .right secondSlope)
    (slopes : firstSlope < secondSlope) :
    (portBoundaryAnchor graph drawing first).2+2 ≤ (portBoundaryAnchor graph drawing second).2 := by
  have ordered := right_portBoundaryAnchor_order distinct degree firstMember secondMember sameVertex firstKey secondKey slopes
  have firstOdd := portBoundaryAnchor_horizontal_odd distinct degree firstMember
    (by simp [firstKey,StraightRayKey.group])
  have secondOdd := portBoundaryAnchor_horizontal_odd distinct degree secondMember
    (by simp [secondKey,StraightRayKey.group])
  omega

theorem left_portBoundaryAnchor_gap {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) {firstSlope secondSlope : ℚ}
    (firstKey : drawing.portRayKey first = .left firstSlope) (secondKey : drawing.portRayKey second = .left secondSlope)
    (slopes : firstSlope < secondSlope) :
    (portBoundaryAnchor graph drawing second).2+2 ≤ (portBoundaryAnchor graph drawing first).2 := by
  have ordered := left_portBoundaryAnchor_order distinct degree firstMember secondMember sameVertex firstKey secondKey slopes
  have firstOdd := portBoundaryAnchor_horizontal_odd distinct degree firstMember
    (by simp [firstKey,StraightRayKey.group])
  have secondOdd := portBoundaryAnchor_horizontal_odd distinct degree secondMember
    (by simp [secondKey,StraightRayKey.group])
  omega

end LeanTrominoes.OrthogonalDrawingRefinement

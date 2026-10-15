/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightAnchorGeometry
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexRayGroups

/-! # Assigned boundary anchors follow the original incidence slope order -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

theorem anchorProfileOfKeys_perm {first second : List StraightRayKey} (perm : first.Perm second) :
    anchorProfileOfKeys first = anchorProfileOfKeys second := by
  have leftCount := perm.countP_eq StraightRayKey.isLeft
  have rightCount := perm.countP_eq StraightRayKey.isRight
  have upMember : StraightRayKey.up ∈ first ↔ StraightRayKey.up ∈ second := perm.mem_iff
  have downMember : StraightRayKey.down ∈ first ↔ StraightRayKey.down ∈ second := perm.mem_iff
  simp only [anchorProfileOfKeys,leftCount,rightCount,upMember,downMember]

theorem vertexAnchorProfile_anchorGroups {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    (vertex : Vertex) :
    (vertexAnchorProfile graph drawing vertex).anchorGroups =
      (orderedIncidences graph drawing vertex).map (fun port => (drawing.portRayKey port).group) := by
  have mapped := (orderedIncidences_perm graph drawing vertex).map drawing.portRayKey
  have nodup := mapped.nodup_iff.mpr (drawing.portRayKeys_nodup distinct vertex)
  have bound : ((orderedIncidences graph drawing vertex).map drawing.portRayKey).length ≤ 4 := by
    rw [List.length_map,(orderedIncidences_perm graph drawing vertex).length_eq,portsAt_length]
    exact degree vertex
  have ordered : ((orderedIncidences graph drawing vertex).map drawing.portRayKey).Pairwise
      (fun first second => first.clockwiseCode ≤ second.clockwiseCode) :=
    (orderedIncidences_ordered graph drawing vertex).map drawing.portRayKey (fun _ _ ordered => ordered)
  have profileEq := anchorProfileOfKeys_perm mapped
  change (anchorProfileOfKeys ((portsAt graph vertex).map drawing.portRayKey)).anchorGroups = _
  rw [← profileEq,rayGroups_eq_anchorGroups nodup bound ordered]
  simp only [List.map_map,Function.comp_def]

theorem incidenceAnchor_group {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (vertexAnchorProfile graph drawing port.vertex).anchorGroups[(incidenceAnchorIndex graph drawing port).val]? =
      some (drawing.portRayKey port).group := by
  rw [vertexAnchorProfile_anchorGroups distinct degree,incidenceAnchorIndex_val_eq degree member,List.getElem?_map]
  have rank := List.idxOf_lt_length_iff.mpr ((orderedIncidences_mem graph drawing port.vertex port).mpr ⟨member,rfl⟩)
  simp only [List.getElem?_eq_getElem rank,List.getElem_idxOf rank,Option.map_some]

def portBoundaryAnchor {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : Cell :=
  (vertexAnchorProfile graph drawing port.vertex).anchors[(incidenceAnchorIndex graph drawing port).val]?.getD (0,0)

theorem incidenceTemplate_last_some {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (incidenceTemplate graph drawing port).getLast? = some (portBoundaryAnchor graph drawing port) := by
  have valid : (incidenceAnchorIndex graph drawing port).val < (vertexAnchorProfile graph drawing port.vertex).anchors.length := by
    rw [AnchorProfile.anchors_length]
    exact incidenceAnchorIndex_valid distinct degree member
  rw [incidenceTemplate_last distinct degree member]
  simp only [portBoundaryAnchor,List.getElem?_eq_getElem valid,Option.getD_some]

theorem portBoundaryAnchor_x {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (portBoundaryAnchor graph drawing port).1 = groupBoundaryX (drawing.portRayKey port).group := by
  rw [portBoundaryAnchor,AnchorProfile.anchor_x_matches_group _ _
    (vertexAnchorProfile_degree_le_four distinct degree _) (incidenceAnchorIndex_valid distinct degree member),
    incidenceAnchor_group distinct degree member]
  rfl

theorem incidenceAnchorIndex_lt_of_code_lt {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex)
    (ordered : (drawing.portRayKey first).clockwiseCode < (drawing.portRayKey second).clockwiseCode) :
    (incidenceAnchorIndex graph drawing first).val < (incidenceAnchorIndex graph drawing second).val := by
  rw [incidenceAnchorIndex_val_eq degree firstMember,incidenceAnchorIndex_val_eq degree secondMember,← sameVertex]
  have firstAt := (orderedIncidences_mem graph drawing first.vertex first).mpr ⟨firstMember,rfl⟩
  have secondAt := (orderedIncidences_mem graph drawing first.vertex second).mpr ⟨secondMember,sameVertex.symm⟩
  have firstValid := List.idxOf_lt_length_iff.mpr firstAt
  have secondValid := List.idxOf_lt_length_iff.mpr secondAt
  by_contra wrong
  rcases lt_or_eq_of_le (Nat.le_of_not_gt wrong) with reverse | sameIndex
  · have reversed := List.pairwise_iff_getElem.mp (orderedIncidences_strict distinct first.vertex)
      _ _ secondValid firstValid reverse
    simp only [List.getElem_idxOf] at reversed
    exact (not_lt_of_gt ordered) reversed
  · have equal : first = second := (List.idxOf_inj firstAt).mp sameIndex.symm
    rw [equal] at ordered
    exact (lt_irrefl _) ordered

theorem right_portBoundaryAnchor_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) {firstSlope secondSlope : ℚ}
    (firstKey : drawing.portRayKey first = .right firstSlope) (secondKey : drawing.portRayKey second = .right secondSlope)
    (slopes : firstSlope < secondSlope) :
    (portBoundaryAnchor graph drawing first).2 < (portBoundaryAnchor graph drawing second).2 := by
  have codes : (drawing.portRayKey second).clockwiseCode < (drawing.portRayKey first).clockwiseCode := by
    rw [firstKey,secondKey]
    simpa [StraightRayKey.clockwiseCode,Prod.Lex.toLex_lt_toLex] using neg_lt_neg slopes
  have ranks := incidenceAnchorIndex_lt_of_code_lt distinct degree secondMember firstMember sameVertex.symm codes
  have secondValid := incidenceAnchorIndex_valid distinct degree secondMember
  rw [← sameVertex] at secondValid
  have firstGroup := incidenceAnchor_group distinct degree firstMember
  have secondGroup := incidenceAnchor_group distinct degree secondMember
  rw [firstKey] at firstGroup
  rw [secondKey,← sameVertex] at secondGroup
  have result := AnchorProfile.right_anchor_ordinates (vertexAnchorProfile graph drawing first.vertex)
    (incidenceAnchorIndex graph drawing second) (incidenceAnchorIndex graph drawing first)
    (vertexAnchorProfile_degree_le_four distinct degree _) secondValid
    (incidenceAnchorIndex_valid distinct degree firstMember) ranks secondGroup firstGroup
  simpa only [portBoundaryAnchor,← sameVertex] using result

theorem left_portBoundaryAnchor_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) {firstSlope secondSlope : ℚ}
    (firstKey : drawing.portRayKey first = .left firstSlope) (secondKey : drawing.portRayKey second = .left secondSlope)
    (slopes : firstSlope < secondSlope) :
    (portBoundaryAnchor graph drawing second).2 < (portBoundaryAnchor graph drawing first).2 := by
  have codes : (drawing.portRayKey second).clockwiseCode < (drawing.portRayKey first).clockwiseCode := by
    rw [firstKey,secondKey]
    simpa [StraightRayKey.clockwiseCode,Prod.Lex.toLex_lt_toLex] using neg_lt_neg slopes
  have ranks := incidenceAnchorIndex_lt_of_code_lt distinct degree secondMember firstMember sameVertex.symm codes
  have secondValid := incidenceAnchorIndex_valid distinct degree secondMember
  rw [← sameVertex] at secondValid
  have firstGroup := incidenceAnchor_group distinct degree firstMember
  have secondGroup := incidenceAnchor_group distinct degree secondMember
  rw [firstKey] at firstGroup
  rw [secondKey,← sameVertex] at secondGroup
  have result := AnchorProfile.left_anchor_ordinates (vertexAnchorProfile graph drawing first.vertex)
    (incidenceAnchorIndex graph drawing second) (incidenceAnchorIndex graph drawing first)
    (vertexAnchorProfile_degree_le_four distinct degree _) secondValid
    (incidenceAnchorIndex_valid distinct degree firstMember) ranks secondGroup firstGroup
  simpa only [portBoundaryAnchor,← sameVertex] using result

end LeanTrominoes.OrthogonalDrawingRefinement

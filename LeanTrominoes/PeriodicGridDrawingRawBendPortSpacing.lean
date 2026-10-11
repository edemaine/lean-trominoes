/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanGeometry

/-! # Actual horizontal ports have the spacing required by digital cores

The same two-unit gap holds at original vertices and inserted bends. The
bend assignment orders the two actual ports by their outward ray heights.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem bendPortIndex_order {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {edgeIndex pointIndex : Nat} (vertexMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex))
    (secondMember : second ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex))
    (ordered : BendFan.outwardHeight ((shiftedDrawing source drawing).portRayKey first) <
      BendFan.outwardHeight ((shiftedDrawing source drawing).portRayKey second)) :
    bendPortIndex source drawing edgeIndex pointIndex first = true ∧
      bendPortIndex source drawing edgeIndex pointIndex second = false := by
  have nodup := portsAt_nodup (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)
  rw [bend_ports_eq vertexMember] at firstMember secondMember nodup
  have different : bendFirstPort source drawing edgeIndex pointIndex ≠ bendSecondPort source drawing edgeIndex pointIndex := by
    simpa using nodup
  simp only [List.mem_cons,List.not_mem_nil,or_false] at firstMember secondMember
  rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl
  · exact (lt_irrefl _ ordered).elim
  · simp [bendPortIndex,BendFan.assignedIndex,ordered,different.symm]
  · simp [bendPortIndex,BendFan.assignedIndex,not_lt_of_gt ordered,different.symm]
  · exact (lt_irrefl _ ordered).elim

theorem bend_fanAnchor_horizontal_gap {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {edgeIndex pointIndex : Nat}
    (vertexMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex))
    (secondMember : second ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex))
    (firstVertex : first.vertex = .bend edgeIndex pointIndex)
    (secondVertex : second.vertex = .bend edgeIndex pointIndex)
    (same : BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey first) =
      BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey second))
    (nonzero : BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey first) ≠ 0)
    (ordered : BendFan.outwardHeight ((shiftedDrawing source drawing).portRayKey first) <
      BendFan.outwardHeight ((shiftedDrawing source drawing).portRayKey second)) :
    (fanAnchor source drawing first).2+2 ≤ (fanAnchor source drawing second).2 := by
  obtain ⟨firstIndex,secondIndex⟩ := bendPortIndex_order vertexMember firstMember secondMember ordered
  have firstClass := bendPortIndex_class vertexMember firstMember
  have secondClass := bendPortIndex_class vertexMember secondMember
  simp only [firstIndex,ite_true] at firstClass
  simp [secondIndex] at secondClass
  have sameSide : (bendProfile source drawing edgeIndex pointIndex).sameSide := by
    simp only [BendFan.Profile.sameSide,firstClass,secondClass,BendFan.rayClass_horizontalSign]
    exact ⟨same.symm,fun zero => nonzero (same.trans zero)⟩
  have gap := BendFan.sameSide_port_gap _ (bendProfile_valid planar vertexMember) sameSide
  simpa only [fanAnchor,fanRoute,firstVertex,secondVertex,firstIndex,secondIndex,BendFan.Profile.port] using gap

theorem fanAnchor_original {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing))
    {value : V} (vertex : port.vertex = .original value) :
    fanAnchor source drawing port = portBoundaryAnchor (subdivisionGraph source drawing) (shiftedDrawing source drawing) port := by
  have last := incidenceTemplate_last_some (shifted_distinctPortRayKeys planar)
    (subdivisionGraph_degreeAtMost degree (by decide) drawing) member
  simp only [fanAnchor,fanRoute,vertex,last,Option.getD_some]

theorem fanAnchor_right_gap {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ allPorts (subdivisionGraph source drawing))
    (secondMember : second ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : first.vertex = second.vertex) {firstSlope secondSlope : ℚ}
    (firstKey : (shiftedDrawing source drawing).portRayKey first = .right firstSlope)
    (secondKey : (shiftedDrawing source drawing).portRayKey second = .right secondSlope)
    (slopes : firstSlope < secondSlope) :
    (fanAnchor source drawing first).2+2 ≤ (fanAnchor source drawing second).2 := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) firstMember
  cases vertex : first.vertex with
  | original value =>
      rw [fanAnchor_original planar degree firstMember vertex,
        fanAnchor_original planar degree secondMember (sameVertex.symm.trans vertex)]
      exact right_portBoundaryAnchor_gap (shifted_distinctPortRayKeys planar)
        (subdivisionGraph_degreeAtMost degree (by decide) drawing) firstMember secondMember sameVertex firstKey secondKey slopes
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      apply bend_fanAnchor_horizontal_gap planar vertexMember
        (by simpa only [vertex] using port_mem_portsAt _ firstMember)
        (by simpa only [← sameVertex,vertex] using port_mem_portsAt _ secondMember)
        vertex (sameVertex.symm.trans vertex)
      · simp [firstKey,secondKey,BendFan.horizontalSign]
      · simp [firstKey,BendFan.horizontalSign]
      · simpa only [firstKey,secondKey,BendFan.outwardHeight] using slopes

theorem fanAnchor_left_gap {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ allPorts (subdivisionGraph source drawing))
    (secondMember : second ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : first.vertex = second.vertex) {firstSlope secondSlope : ℚ}
    (firstKey : (shiftedDrawing source drawing).portRayKey first = .left firstSlope)
    (secondKey : (shiftedDrawing source drawing).portRayKey second = .left secondSlope)
    (slopes : firstSlope < secondSlope) :
    (fanAnchor source drawing second).2+2 ≤ (fanAnchor source drawing first).2 := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) firstMember
  cases vertex : first.vertex with
  | original value =>
      rw [fanAnchor_original planar degree firstMember vertex,
        fanAnchor_original planar degree secondMember (sameVertex.symm.trans vertex)]
      exact left_portBoundaryAnchor_gap (shifted_distinctPortRayKeys planar)
        (subdivisionGraph_degreeAtMost degree (by decide) drawing) firstMember secondMember sameVertex firstKey secondKey slopes
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      apply bend_fanAnchor_horizontal_gap planar vertexMember
        (by simpa only [← sameVertex,vertex] using port_mem_portsAt _ secondMember)
        (by simpa only [vertex] using port_mem_portsAt _ firstMember)
        (sameVertex.symm.trans vertex) vertex
      · simp [firstKey,secondKey,BendFan.horizontalSign]
      · simp [secondKey,BendFan.horizontalSign]
      · simpa only [firstKey,secondKey,BendFan.outwardHeight,neg_lt_neg_iff] using slopes

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

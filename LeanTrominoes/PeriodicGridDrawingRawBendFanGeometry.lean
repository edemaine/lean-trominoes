/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendFanAssignment
import LeanTrominoes.PeriodicGridDrawingAnchorBoundarySpacing
import LeanTrominoes.GridSegmentBoundedCoreTubes

/-! # Constant fan bounds and the straight cores between their anchors -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing OrthogonalDrawingRefinement

def fanAnchor {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) : Cell := (fanRoute source drawing port).getLast?.getD (0,0)

theorem fanRoute_nonempty {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) : fanRoute source drawing port ≠ [] := by
  intro empty
  have head := fanRoute_head source drawing port
  simp [empty] at head

theorem fanRoute_last {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) : (fanRoute source drawing port).getLast? = some (fanAnchor source drawing port) := by
  simp only [fanAnchor,List.getLast?_eq_getLast_of_ne_nil (fanRoute_nonempty source drawing port),Option.getD_some]

theorem fanRoute_bounds {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) :
    ∀ point ∈ fanRoute source drawing port, -5 ≤ point.1 ∧ point.1 ≤ 5 ∧ -10 ≤ point.2 ∧ point.2 ≤ 10 := by
  unfold fanRoute
  cases port.vertex
  · exact rectangleTemplate_points_in_rectangle _ _
  · exact BendFan.route_bounds _ _

theorem fanAnchor_bounds {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) : |(fanAnchor source drawing port).1| ≤ 5 ∧ |(fanAnchor source drawing port).2| ≤ 10 := by
  have bounds := fanRoute_bounds source drawing port _ (mem_of_getLast?_eq_some (fanRoute_last source drawing port))
  exact ⟨abs_le.mpr ⟨bounds.1,bounds.2.1⟩,abs_le.mpr ⟨bounds.2.2.1,bounds.2.2.2⟩⟩

theorem bendPortIndex_class {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {edgeIndex pointIndex : Nat} (vertexMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices)
    {port : GraphPort (Vertex V)} (member : port ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)) :
    (if bendPortIndex source drawing edgeIndex pointIndex port then (bendProfile source drawing edgeIndex pointIndex).second
      else (bendProfile source drawing edgeIndex pointIndex).first) =
      BendFan.rayClass ((shiftedDrawing source drawing).portRayKey port) := by
  have nodup := portsAt_nodup (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)
  rw [bend_ports_eq vertexMember] at member nodup
  have different : bendFirstPort source drawing edgeIndex pointIndex ≠ bendSecondPort source drawing edgeIndex pointIndex := by
    simpa using nodup
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · simpa only [bendPortIndex,if_pos rfl,ite_true,bendProfile] using BendFan.assignedProfile_first_class
      ((shiftedDrawing source drawing).portRayKey (bendFirstPort source drawing edgeIndex pointIndex))
      ((shiftedDrawing source drawing).portRayKey (bendSecondPort source drawing edgeIndex pointIndex))
  · simpa only [bendPortIndex,if_neg different.symm,bendProfile] using BendFan.assignedProfile_second_class
      ((shiftedDrawing source drawing).portRayKey (bendFirstPort source drawing edgeIndex pointIndex))
      ((shiftedDrawing source drawing).portRayKey (bendSecondPort source drawing edgeIndex pointIndex))

theorem fanAnchor_x {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {port : GraphPort (Vertex V)} (member : port ∈ allPorts (subdivisionGraph source drawing)) :
    (fanAnchor source drawing port).1 = 5*BendFan.horizontalSign ((shiftedDrawing source drawing).portRayKey port) := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) member
  cases vertex : port.vertex with
  | original value =>
      have last := incidenceTemplate_last_some (shifted_distinctPortRayKeys planar)
        (subdivisionGraph_degreeAtMost degree (by decide) drawing) member
      have anchor : fanAnchor source drawing port = portBoundaryAnchor (subdivisionGraph source drawing) (shiftedDrawing source drawing) port := by
        simp only [fanAnchor,fanRoute,vertex,last,Option.getD_some]
      rw [anchor,portBoundaryAnchor_x (shifted_distinctPortRayKeys planar)
        (subdivisionGraph_degreeAtMost degree (by decide) drawing) member]
      cases (shiftedDrawing source drawing).portRayKey port <;>
        simp [groupBoundaryX,StraightRayKey.group,BendFan.horizontalSign]
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      have atBend : port ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) := by
        simpa only [vertex] using port_mem_portsAt (subdivisionGraph source drawing) member
      have boundary := (BendFan.port_boundary (bendProfile source drawing edgeIndex pointIndex)
        (bendPortIndex source drawing edgeIndex pointIndex port) (bendProfile_valid planar vertexMember)).1
      rw [bendPortIndex_class vertexMember atBend,BendFan.rayClass_horizontalSign] at boundary
      simpa only [fanAnchor,fanRoute,vertex,BendFan.Profile.port] using boundary

def anchoredSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (tagged : PeriodicEdge (Vertex V) × Nat) : GridSegment :=
  ⟨Cell.add (Cell.scale factor (subdivisionSegment source drawing tagged.1).start)
      (fanAnchor source drawing (sourcePort tagged.1 tagged.2)),
    Cell.add (Cell.scale factor (subdivisionSegment source drawing tagged.1).finish)
      (fanAnchor source drawing (targetPort tagged.1 tagged.2))⟩

theorem anchoredSegment_perturbed {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Int) (tagged : PeriodicEdge (Vertex V) × Nat) :
    GridSegment.BoundedEndpointPerturbation 10 factor (subdivisionSegment source drawing tagged.1)
      (anchoredSegment source drawing factor tagged) := by
  have first := fanAnchor_bounds source drawing (sourcePort tagged.1 tagged.2)
  have last := fanAnchor_bounds source drawing (targetPort tagged.1 tagged.2)
  simp only [GridSegment.BoundedEndpointPerturbation,anchoredSegment,Cell.add,Cell.scale,add_sub_cancel_left]
  exact ⟨⟨first.1.trans (by norm_num),first.2⟩,⟨last.1.trans (by norm_num),last.2⟩⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

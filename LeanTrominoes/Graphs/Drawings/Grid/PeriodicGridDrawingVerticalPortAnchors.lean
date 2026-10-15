/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexVerticalAnchors
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingAnchorBoundaryOrder
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingPieceWindow

/-! # Vertical edge endpoints select opposite vertical boundary anchors -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

theorem portBoundaryAnchor_of_up {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (up : drawing.portRayKey port = .up) :
    portBoundaryAnchor graph drawing port = (0,10) := by
  apply AnchorProfile.up_anchor _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree member)
  rw [incidenceAnchor_group distinct degree member,up]
  rfl

theorem portBoundaryAnchor_of_down {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (down : drawing.portRayKey port = .down) :
    portBoundaryAnchor graph drawing port = (0,-10) := by
  apply AnchorProfile.down_anchor _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree member)
  rw [incidenceAnchor_group distinct degree member,down]
  rfl

theorem vertical_endpoint_anchors {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    if (drawing.straightSegment tagged.2).start.2 < (drawing.straightSegment tagged.2).finish.2 then
      portBoundaryAnchor graph drawing (sourcePort tagged.1 tagged.2) = (0,10) ∧
        portBoundaryAnchor graph drawing (targetPort tagged.1 tagged.2) = (0,-10)
    else portBoundaryAnchor graph drawing (sourcePort tagged.1 tagged.2) = (0,-10) ∧
      portBoundaryAnchor graph drawing (targetPort tagged.1 tagged.2) = (0,10) := by
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have oldX : (drawing.straightSegment tagged.2).start.1 = (drawing.straightSegment tagged.2).finish.1 := by
    simpa [liftedStraightSegment,GridSegment.translate,Cell.add] using vertical
  have nondegenerate := straightSegment_nondegenerate planar.1 member (straight _ member)
  have differentY : (drawing.straightSegment tagged.2).start.2 ≠ (drawing.straightSegment tagged.2).finish.2 :=
    fun same => nondegenerate (Prod.ext oldX same)
  split_ifs with forward
  · refine ⟨portBoundaryAnchor_of_up distinct degree (sourcePort_mem_allPorts graph member) ?_,
      portBoundaryAnchor_of_down distinct degree (targetPort_mem_allPorts graph member) ?_⟩
    · simp [portRayKey,sourcePort,GridSegment.straightRayKey,oldX,forward]
    · simp [portRayKey,targetPort,GridSegment.straightRayKey,GridSegment.reverse,oldX,not_lt_of_ge forward.le]
  · have backward : (drawing.straightSegment tagged.2).finish.2 < (drawing.straightSegment tagged.2).start.2 := by omega
    refine ⟨portBoundaryAnchor_of_down distinct degree (sourcePort_mem_allPorts graph member) ?_,
      portBoundaryAnchor_of_up distinct degree (targetPort_mem_allPorts graph member) ?_⟩
    · simp [portRayKey,sourcePort,GridSegment.straightRayKey,oldX,forward]
    · simp [portRayKey,targetPort,GridSegment.straightRayKey,GridSegment.reverse,oldX,backward]

end LeanTrominoes.PeriodicGridDrawing

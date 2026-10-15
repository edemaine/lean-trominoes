/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedFanContacts
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendNonincidentFanCores
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedVertexUniqueness

/-! # A core–fan contact identifies the core's own endpoint incidence -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem raw_segment_vertex_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {vertex : Vertex V}
    (vertexMember : vertex ∈ (subdivisionGraph source drawing).vertices)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (copy vertexCopy : Cell)
    (contains : ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).RealContains
      (realCell (Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy)))) :
    realCell (Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy)) =
        realCell ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).start ∨
      realCell (Cell.add (position source drawing vertex) (drawing.periodTranslation vertexCopy)) =
        realCell ((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).finish := by
  have positionMember : position source drawing vertex ∈ (subdivisionDrawing source drawing).vertexPositions :=
    List.mem_map.mpr ⟨vertex,vertexMember,rfl⟩
  have routeValid : tagged.2 < (subdivisionDrawing source drawing).edgeRoutes.length := by
    simpa only [subdivisionDrawing,List.length_map,Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have endpoint := subdivision_verticesAvoidRoutes planar _ positionMember vertexCopy copy _ routeValid
    ((subdivision_segment_image source drawing member copy _).mpr contains)
  exact (subdivision_segment_endpoints source drawing member copy _).mp endpoint

theorem liftedCoreRoute_fan_contact_identifies_port {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (copy fanCopy : Cell) {port : GraphPort (Vertex V)} (portMember : port ∈ allPorts (subdivisionGraph source drawing))
    {point : ℝ × ℝ} (coreContains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point)
    (fanContains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (Cell.add (position source drawing port.vertex) (drawing.periodTranslation fanCopy)) port) point) :
    ∃ target : Bool, incidentPort tagged target = port ∧ incidentCopy tagged target copy = fanCopy ∧
      point = realCell ((liftedIncidentAnchoredSegment source drawing tagged target copy).scale (Cubic.rasterFactor drawing.gridSize)).start := by
  classical
  let center := Cell.add (position source drawing port.vertex) (drawing.periodTranslation fanCopy)
  by_cases avoids : ¬((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).RealContains (realCell center)
  · exact (liftedCoreRoute_avoids_nonincident_fan planar graphLocal drawingLocal member copy center port avoids coreContains fanContains).elim
  · have originalContains := not_not.mp avoids
    have portVertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) portMember
    have endpoints := raw_segment_vertex_contact planar portVertexMember member copy fanCopy originalContains
    obtain ⟨target,atEndpoint⟩ : ∃ target : Bool, center = (liftedIncidentRawSegment source drawing tagged target copy).start := by
      rcases endpoints with endpoint | endpoint
      · exact ⟨false,realCell_injective endpoint⟩
      · exact ⟨true,realCell_injective endpoint⟩
    have data := incidentCoreData planar degree graphLocal drawingLocal member target
    have unique := raw_lifted_vertex_eq planar
      (port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) data.member) portVertexMember
      (by rw [← liftedIncidentRawSegment_start]; exact atEndpoint.symm)
    change GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) center port) point at fanContains
    rw [atEndpoint] at fanContains
    by_cases equal : incidentPort tagged target = port
    · exact ⟨target,equal,unique.2,liftedCoreRoute_incidentFan_contact planar degree graphLocal drawingLocal member target copy port coreContains fanContains⟩
    · exact (liftedCoreRoute_avoids_other_incident_fan planar degree graphLocal drawingLocal member target copy portMember unique.1 equal
        coreContains fanContains).elim

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendPerturbationGeometry
import LeanTrominoes.GridPolylineRealEndpointMap
import LeanTrominoes.GridPolylineRealSegmentContacts

/-! # Segment and endpoint transport in moved periodic polygonal routes -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing PeriodicOrthocrossing

def liftedPoint (drawing : PeriodicGridDrawing) (factor : Nat) (translate base : Cell) : Cell :=
  Cell.add (Cell.scale ((factor:Int)*drawing.gridSize) translate) (point drawing.gridSize factor base)

theorem perturbDrawing_realEdgeRoute (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0<factor)
    (index : Nat) (translate : Cell) :
    (perturbDrawing drawing factor).realEdgeRoute index translate=
      (drawing.edgeRoute index).map (liftedPoint drawing factor translate) := by
  simp only [realEdgeRoute,perturbDrawing_edgeRoute,periodTranslation,perturbDrawing_gridSize drawing positive,
    Nat.cast_mul,List.map_map,Function.comp_def]
  rfl

theorem moved_segment_provenance {drawing : PeriodicGridDrawing} {factor index : Nat} (positive : 0<factor)
    {translate : Cell} {p : ℝ × ℝ}
    (contains : GridPolyline.RealContains ((perturbDrawing drawing factor).realEdgeRoute index translate) p) :
    ∃ segment∈gridPolylineSegments (drawing.edgeRoute index),
      (segment.mapPoints (liftedPoint drawing factor translate)).RealContains p := by
  rw [perturbDrawing_realEdgeRoute drawing positive] at contains
  obtain ⟨segment,member,contains⟩ := contains
  rw [gridPolylineSegments_map_points] at member
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  exact ⟨old,oldMember,contains⟩

theorem lifted_segment_in_route {drawing : PeriodicGridDrawing} {index : Nat} {translate : Cell}
    {segment : GridSegment} (member : segment∈gridPolylineSegments (drawing.edgeRoute index))
    {p : ℝ × ℝ} (contains : (segment.translate (drawing.periodTranslation translate)).RealContains p) :
    GridPolyline.RealContains (drawing.realEdgeRoute index translate) p := by
  change GridPolyline.RealContains (translatePolyline (drawing.periodTranslation translate) (drawing.edgeRoute index)) p
  exact ⟨segment.translate (drawing.periodTranslation translate),
    by rw [gridPolylineSegments_translatePolyline]; exact List.mem_map.mpr ⟨segment,member,rfl⟩,contains⟩

theorem lifted_endpoint_transport {drawing : PeriodicGridDrawing} {factor index : Nat} (positive : 0<factor)
    {translate base : Cell}
    (endpoint : GridPolyline.RealIsEndpoint (drawing.realEdgeRoute index translate)
      (realCell (Cell.add (drawing.periodTranslation translate) base))) :
    GridPolyline.RealIsEndpoint ((perturbDrawing drawing factor).realEdgeRoute index translate)
      (realCell (liftedPoint drawing factor translate base)) := by
  have injective : Function.Injective (Cell.add (drawing.periodTranslation translate)) := by
    intro first second equal
    have x := congrArg Prod.fst equal
    have y := congrArg Prod.snd equal
    exact Prod.ext (by simp only [Cell.add] at x; omega) (by simp only [Cell.add] at y; omega)
  have baseEndpoint := (GridPolyline.realIsEndpoint_map_at_cell_iff _ injective).mp endpoint
  rw [perturbDrawing_realEdgeRoute drawing positive]
  exact baseEndpoint.map_at_cell _

theorem liftedPoint_at_vertex {drawing : PeriodicGridDrawing} {factor : Nat} {vertex base : Cell}
    (bounds : drawing.PositionInFundamentalSquare vertex) (routeCell vertexCell : Cell)
    (equal : Cell.add (drawing.periodTranslation routeCell) base=Cell.add vertex (drawing.periodTranslation vertexCell)) :
    liftedPoint drawing factor routeCell base=
      Cell.add (Cell.scale factor vertex) (Cell.scale ((factor:Int)*drawing.gridSize) vertexCell) := by
  have old := lifted_point_at_vertex (factor := (factor:Int)) bounds routeCell vertexCell
    (by simpa only [periodTranslation,Cell.add,add_comm] using equal)
  simpa only [liftedPoint,Cell.add,add_comm] using old

theorem moved_lifted_segment_perturbed (drawing : PeriodicGridDrawing) (factor : Nat)
    (segment : GridSegment) (translate : Cell) :
    GridSegment.EndpointPerturbation factor (segment.translate (drawing.periodTranslation translate))
      (segment.mapPoints (liftedPoint drawing factor translate)) :=
  lifted_segment_perturbation drawing.gridSize factor segment translate

theorem simple_segment_endpoint_of_mem {route : List Cell} (simple : GridPolyline.IsRealSimple route)
    {segment : GridSegment} (member : segment∈gridPolylineSegments route)
    {p : ℝ × ℝ} (endpoint : GridPolyline.RealIsEndpoint route p) (contains : segment.RealContains p) :
    p=realCell segment.start ∨ p=realCell segment.finish := by
  let index := (gridPolylineSegments route).idxOf segment
  have valid : index<(gridPolylineSegments route).length := List.idxOf_lt_length_of_mem member
  have lookup : (gridPolylineSegments route)[index]=segment := List.getElem_idxOf valid
  have taggedMember : (segment,index)∈(gridPolylineSegments route).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨valid,lookup⟩
  exact simple.endpoint_segment_contact taggedMember endpoint contains

end LeanTrominoes.PeriodicGridDrawing.InteriorBends

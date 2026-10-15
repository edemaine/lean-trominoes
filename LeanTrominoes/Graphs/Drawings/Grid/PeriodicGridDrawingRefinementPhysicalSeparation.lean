/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRefinementPhysicalImages
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEndpointFanOccurrences
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleBarOccurrenceSeparation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCoreOccurrenceSeparation

/-! # Distinct periodic edge routes can share only graph vertices -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

def RefinementFanContains {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat)
    (cell : Cell) (point : ℝ × ℝ) : Prop :=
  ∃ target, GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (endpointPort tagged target)
    (endpointFanCell tagged target cell)) point

def RefinementNonfanContains {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat)
    (shift : Cell) (point : ℝ × ℝ) : Prop :=
  (∃ column, column < drawing.gridSize ∧ ∃ cell piece,
    rectangleEdgePiece? graph drawing tagged.2 column cell = some piece ∧
      GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point) ∨
  (∃ line, (drawing.liftedStraightSegment tagged.2 shift).CrossesVerticalLine line ∧
    GridPolyline.RealContains (paddedCrossingRoute graph drawing line (tagged.2,shift)) point) ∨
  ((drawing.liftedStraightSegment tagged.2 (0,0)).start.1 = (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 ∧
    ((drawing.liftedStraightSegment tagged.2 shift).verticalCore (paddedRefinementFactor drawing.gridSize)
      (crossingBound drawing.gridSize)).RealContains point)

theorem refinementPhysicalContains_fan_or_nonfan {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} {tagged : PeriodicEdge Vertex × Nat}
    {cell : Cell} {point : ℝ × ℝ} (contains : RefinementPhysicalContains graph drawing tagged cell point) :
    RefinementFanContains graph drawing tagged cell point ∨ RefinementNonfanContains graph drawing tagged cell point := by
  rcases contains with source | target | rectangle | bar | core
  · exact Or.inl ⟨false,source⟩
  · exact Or.inl ⟨true,target⟩
  · exact Or.inr (Or.inl rectangle)
  · exact Or.inr (Or.inr (Or.inl bar))
  · exact Or.inr (Or.inr (Or.inr core))

theorem liftedStraightSegment_isVertical_of_zero {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) (cell : Cell) :
    (drawing.liftedStraightSegment tagged.2 cell).IsVertical := by
  have oldX : (drawing.straightSegment tagged.2).start.1 = (drawing.straightSegment tagged.2).finish.1 := by
    simpa [liftedStraightSegment,GridSegment.translate,Cell.add] using vertical
  have sameX : (drawing.liftedStraightSegment tagged.2 cell).start.1 = (drawing.liftedStraightSegment tagged.2 cell).finish.1 := by
    simp [liftedStraightSegment,GridSegment.translate,Cell.add,oldX]
  exact ⟨sameX,fun same => liftedStraightSegment_nondegenerate valid member straight cell (Prod.ext sameX same)⟩

theorem refinement_nonfan_fan_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    (firstCell lastCell : Cell) (different : (first.2,firstCell) ≠ (last.2,lastCell)) {point : ℝ × ℝ}
    (firstContains : RefinementNonfanContains graph drawing first firstCell point)
    (lastContains : RefinementFanContains graph drawing last lastCell point) : False := by
  obtain ⟨target,fanContains⟩ := lastContains
  rcases firstContains with ⟨column,_,cell,piece,lookup,contains⟩ | ⟨line,crosses,contains⟩ | ⟨vertical,contains⟩
  · exact different (rectangleEdgePiece_endpoint_fan_contact_occurrence_eq planar degree graphLocal straight
      first.2 column cell firstCell lookup lastMember target lastCell contains fanContains)
  · have crossing := periodic_crossing_residue_mem planar.1.1 firstMember (straight _ firstMember)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx firstMember)) firstCell crosses
    exact paddedCrossingBar_avoids_incidence_route planar.1.1 degree crossing
      (endpointPort_mem graph lastMember target) (endpointFanCell last target lastCell) contains fanContains
  · exact different (verticalCore_endpoint_fan_contact_occurrence_eq planar degree straight firstMember lastMember vertical
      firstCell target lastCell contains fanContains)

theorem refinement_nonfan_nonfan_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    (firstCell lastCell : Cell) (different : (first.2,firstCell) ≠ (last.2,lastCell)) {point : ℝ × ℝ}
    (firstContains : RefinementNonfanContains graph drawing first firstCell point)
    (lastContains : RefinementNonfanContains graph drawing last lastCell point) : False := by
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  rcases firstContains with ⟨fc,fb,fcell,fp,fl,fx⟩ | ⟨fline,fcross,fx⟩ | ⟨fv,fx⟩
  · rcases lastContains with ⟨lc,lb,lcell,lp,ll,lx⟩ | ⟨lline,lcross,lx⟩ | ⟨lv,lx⟩
    · exact different (rectangleEdgePiece_occurrences_contact_eq planar degree graphLocal straight first.2 last.2 fc lc fb lb
        fcell lcell firstCell lastCell fl ll fx lx)
    · exact different (rectangleEdgePiece_bar_contact_occurrence_eq planar degree graphLocal straight first.2 fc fcell firstCell fl
        lastMember lastCell lline lcross fx lx)
    · exact verticalCore_lifted_avoids_rectangle_piece planar degree graphLocal straight last.2 lastCell
        (liftedStraightSegment_isVertical_of_zero planar.1 lastMember (straight _ lastMember) lv lastCell)
        first.2 fc fcell firstCell fl lx fx
  · rcases lastContains with ⟨lc,_,lcell,lp,ll,lx⟩ | ⟨lline,lcross,lx⟩ | ⟨lv,lx⟩
    · exact different (rectangleEdgePiece_bar_contact_occurrence_eq planar degree graphLocal straight last.2 lc lcell lastCell ll
        firstMember firstCell fline fcross lx fx).symm
    · exact different (paddedCrossingRoutes_contact_identifies_occurrence planar degree graphLocal straight firstMember lastMember
        firstCell lastCell fcross lcross fx lx).2
    · have vertical := liftedStraightSegment_isVertical_of_zero planar.1 lastMember (straight _ lastMember) lv lastCell
      exact scaled_vertical_segment_avoids_crossing_bar planar degree graphLocal lastMember firstMember (straight _ lastMember)
        (straight _ firstMember) lastCell firstCell vertical.1 fcross
        (GridSegment.verticalCore_realContains_parent vertical spacing lx) fx
  · have vertical := liftedStraightSegment_isVertical_of_zero planar.1 firstMember (straight _ firstMember) fv firstCell
    rcases lastContains with ⟨lc,_,lcell,lp,ll,lx⟩ | ⟨lline,lcross,lx⟩ | ⟨lv,lx⟩
    · exact verticalCore_lifted_avoids_rectangle_piece planar degree graphLocal straight first.2 firstCell vertical
        last.2 lc lcell lastCell ll fx lx
    · exact scaled_vertical_segment_avoids_crossing_bar planar degree graphLocal firstMember lastMember (straight _ firstMember)
        (straight _ lastMember) firstCell lastCell vertical.1 lcross
        (GridSegment.verticalCore_realContains_parent vertical spacing fx) lx
    · exact verticalCore_occurrences_disjoint planar firstMember lastMember (straight _ firstMember) (straight _ lastMember)
        firstCell lastCell different vertical
        (liftedStraightSegment_isVertical_of_zero planar.1 lastMember (straight _ lastMember) lv lastCell) fx lx

theorem refinementPhysicalContains_contact_scaled_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    (firstCell lastCell : Cell) (different : (first.2,firstCell) ≠ (last.2,lastCell)) {point : ℝ × ℝ}
    (firstContains : RefinementPhysicalContains graph drawing first firstCell point)
    (lastContains : RefinementPhysicalContains graph drawing last lastCell point) :
    ∃ vertex ∈ drawing.vertexPositions, ∃ cell, point = realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
      (Cell.add vertex (drawing.periodTranslation cell))) := by
  rcases refinementPhysicalContains_fan_or_nonfan firstContains with firstFan | firstNonfan
  · rcases refinementPhysicalContains_fan_or_nonfan lastContains with lastFan | lastNonfan
    · obtain ⟨firstTarget,firstFan⟩ := firstFan
      obtain ⟨lastTarget,lastFan⟩ := lastFan
      have contact := liftedPaddedIncidenceRoutes_contact planar.1.1 (distinctPortRayKeys_of_planar_straight planar straight) degree
        (endpointPort_mem graph firstMember firstTarget) (endpointPort_mem graph lastMember lastTarget)
        (endpointFanCell first firstTarget firstCell) (endpointFanCell last lastTarget lastCell) firstFan lastFan
      have center : point = realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
          (Cell.add (drawing.vertexPosition graph (endpointPort first firstTarget).vertex)
            (drawing.periodTranslation (endpointFanCell first firstTarget firstCell)))) := by
        rcases contact.2.2 with equal | center
        · exact (different (endpointFan_occurrence_injective firstMember lastMember equal contact.2.1)).elim
        · exact center
      exact ⟨_,planar.1.1.vertexPosition_mem (port_vertex_mem planar.1.1.1 (endpointPort_mem graph firstMember firstTarget)),_,center⟩
    · exact (refinement_nonfan_fan_disjoint planar degree graphLocal straight lastMember firstMember lastCell firstCell
        (Ne.symm different) lastNonfan firstFan).elim
  · rcases refinementPhysicalContains_fan_or_nonfan lastContains with lastFan | lastNonfan
    · exact (refinement_nonfan_fan_disjoint planar degree graphLocal straight firstMember lastMember firstCell lastCell different firstNonfan lastFan).elim
    · exact (refinement_nonfan_nonfan_disjoint planar degree graphLocal straight firstMember lastMember firstCell lastCell different firstNonfan lastNonfan).elim

end LeanTrominoes.PeriodicGridDrawing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendParentFanLocality
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendParentOriginalFanLocality
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendParentNodeLabels
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedPieceRoutes

/-! # Both fans of each lifted child stay in the original parent rectangle -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def ParentRectangleContains (drawing : PeriodicGridDrawing) (offset : Cell) (point : ℝ × ℝ) : Prop :=
  (cubicScale drawing : ℝ)*(min 0 ((drawing.gridSize : Int)*offset.1) : Int) ≤ point.1 ∧
    point.1 ≤ (cubicScale drawing : ℝ)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.1) : Int) ∧
    (cubicScale drawing : ℝ)*(min 0 ((drawing.gridSize : Int)*offset.2) : Int) ≤ point.2 ∧
    point.2 ≤ (cubicScale drawing : ℝ)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*offset.2) : Int)

theorem liftedIncidentRawSegment_absolute {V : Type*} [DecidableEq V]
    (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) :
    liftedIncidentRawSegment source drawing tagged target (sourceCell drawing tagged.1.source) =
      if target then (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1).reverse
      else absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1 := by
  cases target <;>
    simp only [liftedIncidentRawSegment,incidentRawSegment,Bool.false_eq_true,ite_false,ite_true,
      ← GridSegment.reverse_translate,subdivisionSegment,periodTranslation,straightRoute_absolute_segment]

theorem parent_piece_fan_inside_rectangle {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (chainMember : tagged.1 ∈ chainEdges (nodes parent (middle drawing parent)))
    (target : Bool) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains
      (liftedPieceFan source drawing tagged target (sourceCell drawing tagged.1.source)) point) :
    ParentRectangleContains drawing parent.1.offset point := by
  rw [liftedPieceFan,liftedIncidentRawSegment_absolute] at contains
  cases target
  · have portMember := sourcePort_mem_allPorts (subdivisionGraph source drawing) member
    cases sourceVertex : tagged.1.source with
    | original vertex =>
      have center : (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1).start =
          Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation (0,0)) := by
        simp only [absoluteSegment,sourceVertex,position,sourceCell,periodTranslation]
      simp only [Bool.false_eq_true,ite_false,incidentPort,center] at contains
      exact original_fanAt_inside_parent_rectangle planar portMember sourceVertex (Or.inl rfl) contains
    | bend edgeIndex pointIndex =>
      have center : (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1).start =
          bendCenter source drawing edgeIndex pointIndex := by
        simp only [absoluteSegment,sourceVertex,bendCenter,periodTranslation]
      simp only [Bool.false_eq_true,ite_false,incidentPort,center] at contains
      exact bend_fanAt_inside_parent_rectangle planar drawingLocal parentMember portMember
        (chain_bend_source_parent drawing parent chainMember sourceVertex) sourceVertex contains
  · have portMember := targetPort_mem_allPorts (subdivisionGraph source drawing) member
    cases targetVertex : tagged.1.target with
    | original vertex =>
      have label := chain_original_target_cell drawing parent chainMember targetVertex
      have center : (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1).finish =
          Cell.add (drawing.vertexPosition source vertex) (drawing.periodTranslation parent.1.offset) := by
        simp only [absoluteSegment,label,targetVertex,position,periodTranslation]
      simp only [ite_true,GridSegment.reverse,incidentPort,center] at contains
      exact original_fanAt_inside_parent_rectangle planar portMember targetVertex (Or.inr rfl) contains
    | bend edgeIndex pointIndex =>
      have labels := chain_bend_target_cell drawing parent chainMember targetVertex
      have center : (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) tagged.1).finish =
          bendCenter source drawing edgeIndex pointIndex := by
        simp only [absoluteSegment,labels.2,targetVertex,bendCenter,periodTranslation]
      simp only [ite_true,GridSegment.reverse,incidentPort,center] at contains
      exact bend_fanAt_inside_parent_rectangle planar drawingLocal parentMember portMember labels.1 targetVertex contains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendParentPieceFanLocality
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedPieceRectangleLocality

/-! # Every complete cubic child stays inside its original parent rectangle -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem parent_piece_inside_rectangle {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (chainMember : tagged.1 ∈ chainEdges (nodes parent (middle drawing parent)))
    {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains
      (liftedPieceRoute source drawing tagged (sourceCell drawing tagged.1.source)) point) :
    ParentRectangleContains drawing parent.1.offset point :=
  liftedPieceRoute_inside_rectangle planar member _
    (fun target _ fanContains => parent_piece_fan_inside_rectangle planar drawingLocal parentMember member chainMember target fanContains)
    contains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

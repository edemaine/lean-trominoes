/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceContactEndpoints

/-! # A rectangle touches a fan at its outer anchor, away from the vertex center -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem rectangleEdgePiece?_fan_outer_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains piece.route point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    point = realCell ((liftedPaddedIncidenceRoute graph drawing port fanCell).getLast?.getD (0,0)) := by
  obtain ⟨chord,chordMember,image⟩ := rectangleEdgePiece?_raw_source planar.1.1 graphLocal straight index column cell lookup
  have raw := (image point).1.mp contains
  have boundary := liftedRectangleInputRoute_column_strip_contact_strip_boundary planar degree graphLocal straight chordMember cell raw
    (Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell)).1
    (enlargedRectangleTemplate_real_bounds _ _ _ _ _ fanContains).1
  have contact := rectangleEdgePiece?_fan_contact_endpoints planar degree graphLocal straight index column cell lookup portMember fanCell contains fanContains
  rcases contact.2 with ⟨endpoint,head,pointEq⟩ | ⟨endpoint,last,pointEq⟩
  · have headEq := enlargedRectangleTemplate_head (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)
      (Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell))
      (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)
    have endpointEq := Option.some.inj (head.symm.trans headEq)
    rw [endpointEq] at pointEq
    have centerX := congrArg Prod.fst pointEq
    simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_natCast] at centerX
    have positive : (0 : ℝ) < crossingBound drawing.gridSize := by exact_mod_cast crossingBound_positive drawing
    rcases boundary with left | right <;> linarith
  · simpa only [last,Option.getD_some] using pointEq

end LeanTrominoes.PeriodicGridDrawing

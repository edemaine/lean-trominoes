/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEndpointOccurrenceInjection
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleFanOccurrenceSeparation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCoreExternalSeparation

/-! # Endpoint-fan contacts recover the parent periodic edge occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

def endpointFanCell {Vertex : Type*} (tagged : PeriodicEdge Vertex × Nat) (target : Bool) (shift : Cell) : Cell :=
  if target then Cell.add tagged.1.offset shift else shift

theorem endpointFan_occurrence_injective {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    {firstTarget lastTarget : Bool} (portsEq : endpointPort first firstTarget = endpointPort last lastTarget)
    {firstCell lastCell : Cell} (cellsEq : endpointFanCell first firstTarget firstCell = endpointFanCell last lastTarget lastCell) :
    (first.2,firstCell) = (last.2,lastCell) := by
  obtain ⟨rfl,rfl⟩ := endpointPort_occurrence_injective firstMember lastMember portsEq
  apply Prod.ext
  · rfl
  change firstCell = lastCell
  cases firstTarget
  · exact cellsEq
  · apply Prod.ext
    · have x := congrArg Prod.fst cellsEq; change _+firstCell.1 = _+lastCell.1 at x; omega
    · have y := congrArg Prod.snd cellsEq; change _+firstCell.2 = _+lastCell.2 at y; omega

theorem rectangleEdgePiece_endpoint_fan_contact_occurrence_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell shift : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {last : PeriodicEdge Vertex × Nat} (lastMember : last ∈ graph.edges.zipIdx) (target : Bool) (lastCell : Cell)
    {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (endpointPort last target)
      (endpointFanCell last target lastCell)) point) :
    (index,shift) = (last.2,lastCell) := by
  obtain ⟨tagged,taggedMember,ownTarget,portEq,parentEq⟩ := rectangleEdgePiece_fan_contact_occurrence_eq planar degree graphLocal straight
    index column cell shift lookup (endpointPort_mem graph lastMember target) (endpointFanCell last target lastCell) contains fanContains
  obtain ⟨rfl,rfl⟩ := endpointPort_occurrence_injective taggedMember lastMember portEq
  cases ownTarget <;> simpa [endpointCell,endpointFanCell,Cell.add,Cell.scale,add_assoc] using parentEq

theorem verticalCore_endpoint_fan_contact_occurrence_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment first.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment first.2 (0,0)).finish.1)
    (firstCell : Cell) (target : Bool) (lastCell : Cell) {point : ℝ × ℝ}
    (coreContains : ((drawing.liftedStraightSegment first.2 firstCell).verticalCore
      (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)).RealContains point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (endpointPort last target)
      (endpointFanCell last target lastCell)) point) :
    (first.2,firstCell) = (last.2,lastCell) := by
  have contact := verticalCore_lifted_fan_contact_identifies_endpoint planar degree straight firstMember vertical
    firstCell (endpointPort_mem graph lastMember target) (endpointFanCell last target lastCell) coreContains fanContains
  rcases contact with ⟨portEq,cellEq⟩ | ⟨portEq,cellEq⟩
  · exact endpointFan_occurrence_injective firstMember lastMember (firstTarget := false) portEq.symm cellEq.symm
  · exact endpointFan_occurrence_injective firstMember lastMember (firstTarget := true) portEq.symm cellEq.symm

end LeanTrominoes.PeriodicGridDrawing

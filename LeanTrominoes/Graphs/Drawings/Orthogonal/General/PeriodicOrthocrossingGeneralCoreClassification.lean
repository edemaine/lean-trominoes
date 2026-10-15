/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralLocal
import LeanTrominoes.Graphs.Drawings.Orthogonal.Classification.PeriodicOrthocrossingClassification

/-! # Semantic roles for the general track-core segments -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def classifiedCore {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    List (ClassifiedSegment Vertex) :=
  let size : Int := drawingGridSize graph
  let source := sourcePort edge edgeIndex
  let target := targetPort edge edgeIndex
  let sourceX := portX graph source
  let targetX := portX graph target
  let sourcePoint : Cell := (sourceX, 3)
  let targetPoint : Cell :=
    Cell.add (targetX, 3) (Cell.scale size edge.offset)
  let low := edgeTrack edgeIndex
  let high := low + 1
  let gate : Int := 3*graph.vertices.length+2*graph.edges.length+4+2*edgeIndex
  match edge.offset with
  | (0, 0) =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (sourceX, low) (targetX, low)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetX, low) targetPoint⟩]
  | (1, 0) =>
      if targetX < sourceX then
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (size + targetX, low)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (size + targetX, low) targetPoint⟩]
      else
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (size, low)⟩,
          ⟨.boundaryVertical edgeIndex,
            GridSegment.mk (size, low) (size, high)⟩,
          ⟨.highHorizontal edgeIndex,
            GridSegment.mk (size, high) (size + targetX, high)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (size + targetX, high) targetPoint⟩]
  | (-1, 0) =>
      if sourceX < targetX then
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (targetX - size, low)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (targetX - size, low) targetPoint⟩]
      else
        [⟨.sourcePortVertical source,
            GridSegment.mk sourcePoint (sourceX, low)⟩,
          ⟨.lowHorizontal edgeIndex,
            GridSegment.mk (sourceX, low) (0, low)⟩,
          ⟨.boundaryVertical edgeIndex,
            GridSegment.mk (0, low) (0, high)⟩,
          ⟨.highHorizontal edgeIndex,
            GridSegment.mk (0, high) (targetX - size, high)⟩,
          ⟨.targetPortVertical target,
            GridSegment.mk (targetX - size, high) targetPoint⟩]
  | (0, 1) =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, high)⟩,
        ⟨.highHorizontal edgeIndex,
          GridSegment.mk (sourceX, high) (gate, high)⟩,
        ⟨.gateVertical edgeIndex,
          GridSegment.mk (gate, high) (gate, size + low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (gate, size + low) (targetX, size + low)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetX, size + low) targetPoint⟩]
  | (0, -1) =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (sourceX, low) (gate, low)⟩,
        ⟨.gateVertical edgeIndex,
          GridSegment.mk (gate, low) (gate, high - size)⟩,
        ⟨.highHorizontal edgeIndex,
          GridSegment.mk (gate, high - size) (targetX, high - size)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetX, high - size) targetPoint⟩]
  | _ =>
      [⟨.sourcePortVertical source,
          GridSegment.mk sourcePoint (sourceX, low)⟩,
        ⟨.lowHorizontal edgeIndex,
          GridSegment.mk (sourceX, low) (targetPoint.1, low)⟩,
        ⟨.targetPortVertical target,
          GridSegment.mk (targetPoint.1, low) targetPoint⟩]

theorem classifiedCore_segments {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (edge : PeriodicEdge Vertex) (index : Nat) :
    (classifiedCore graph edge index).map ClassifiedSegment.segment = gridPolylineSegments (core graph edge index) := by
  unfold classifiedCore core
  split <;> simp_all [gridPolylineSegments]
  all_goals split <;> simp_all [gridPolylineSegments]

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalPortAnchors
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedIncidenceIsolation
import LeanTrominoes.Common.Geometry.GridPolylineRouteWordEndpoints

/-! # Vertical edges join their own endpoint fans through a shortened core -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

def verticalCoreRoute {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) : List Cell :=
  [(paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2)).getLast?.getD (0,0),
    (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).getLast?.getD (0,0)]

def verticalFanRouteWord {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) : List (List Cell) :=
  [paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2),
    verticalCoreRoute graph drawing tagged,
    (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).reverse]

def verticalFanEdgeRoute {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) : List Cell :=
  GridPolyline.joinWord (verticalFanRouteWord graph drawing tagged)

theorem verticalFanRouteWord_long {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) :
    ∀ route ∈ verticalFanRouteWord graph drawing tagged, 2 ≤ route.length := by
  intro route member
  simp only [verticalFanRouteWord,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (paddedIncidenceRoute_isRealOpenSimple graph drawing _).1
  · simp [verticalCoreRoute]
  · simpa only [List.length_reverse] using (liftedPaddedIncidenceRoute_isRealOpenSimple graph drawing _ _).1

theorem verticalFanEdgeRoute_endpoints {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) :
    2 ≤ (verticalFanEdgeRoute graph drawing tagged).length ∧
    (verticalFanEdgeRoute graph drawing tagged).head? =
      some (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source)) ∧
    (verticalFanEdgeRoute graph drawing tagged).getLast? =
      some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
        (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))) := by
  have endpoints := GridPolyline.joinWord_endpoints (verticalFanRouteWord_long graph drawing tagged)
  refine ⟨endpoints.1,?_,?_⟩
  · exact endpoints.2.1.trans (paddedIncidenceRoute_head graph drawing _)
  · unfold verticalFanEdgeRoute verticalFanRouteWord
    rw [endpoints.2.2]
    simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.bind_some,List.getLast?_reverse]
    unfold liftedPaddedIncidenceRoute
    rw [enlargedRectangleTemplate_head]
    apply congrArg some
    apply Prod.ext <;> simp [targetPort,Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring

theorem verticalCoreRoute_coordinates {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    let segment := drawing.straightSegment tagged.2
    let step : Int := if segment.start.2 < segment.finish.2 then 10 else -10
    verticalCoreRoute graph drawing tagged =
      [Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) segment.start)
        (Cell.scale (crossingBound drawing.gridSize) (0,step)),
       Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) segment.finish)
        (Cell.scale (crossingBound drawing.gridSize) (0,-step))] := by
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have sourceLast := paddedIncidenceRoute_last distinct degree (sourcePort_mem_allPorts graph member)
  have targetLast := paddedIncidenceRoute_last distinct degree (targetPort_mem_allPorts graph member)
  have liftedLast : (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).getLast? =
      some (Cell.add (Cell.scale (paddedGridSize drawing.gridSize) tagged.1.offset)
        (Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.target))
          (Cell.scale (crossingBound drawing.gridSize) (portBoundaryAnchor graph drawing (targetPort tagged.1 tagged.2))))) := by
    rw [liftedPaddedIncidenceRoute_eq_translate]
    simp only [translatePolyline,List.getLast?_map,targetLast,Option.map_some]
    rfl
  have oldSource := planar.1.1.2.2.2.2.2 tagged member |>.1
  have oldTarget := planar.1.1.2.2.2.2.2 tagged member |>.2
  have sourceEq : (drawing.straightSegment tagged.2).start = drawing.vertexPosition graph tagged.1.source := by
    simp only [straightSegment,oldSource,Option.getD_some]
  have targetEq : (drawing.straightSegment tagged.2).finish = Cell.add
      (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) := by
    simp only [straightSegment,oldTarget,Option.getD_some]
  have anchors := vertical_endpoint_anchors planar degree straight member vertical
  dsimp only
  unfold verticalCoreRoute
  rw [sourceLast,liftedLast]
  simp only [Option.getD_some]
  split_ifs with forward
  · simp only [if_pos forward] at anchors
    rw [anchors.1,anchors.2,sourceEq,targetEq]
    apply congrArg (fun last => [Cell.add
      (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source))
      (Cell.scale (crossingBound drawing.gridSize) (0,10)),last])
    apply Prod.ext <;> simp [Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring
  · simp only [if_neg forward] at anchors
    rw [anchors.1,anchors.2,sourceEq,targetEq]
    apply congrArg (fun last => [Cell.add
      (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph tagged.1.source))
      (Cell.scale (crossingBound drawing.gridSize) (0,-10)),last])
    apply Prod.ext <;> simp [Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring

end LeanTrominoes.PeriodicGridDrawing

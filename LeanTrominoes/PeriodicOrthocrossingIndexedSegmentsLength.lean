/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingIndexedSegmentsLength
import LeanTrominoes.PeriodicOrthocrossingHorizontalRouteSegmentCount

/-! # Indexed-segment count of the orthocrossing construction -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

theorem drawing_indexedSegments_length_eq_routes
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawing graph).indexedSegments.length =
      (graph.edges.zipIdx.map fun tagged =>
        (gridPolylineSegments
          (constructedEdgeRoute graph tagged.1 tagged.2)).length).sum := by
  rw [PeriodicGridDrawing.indexedSegments_length]
  change ((constructedEdgeRoutes graph).map fun route =>
    (gridPolylineSegments route).length).sum = _
  unfold constructedEdgeRoutes
  simp only [List.map_map, Function.comp_def]

end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawing

/-! # Exact length of the indexed-segment enumeration -/

namespace LeanTrominoes
namespace PeriodicGridDrawing

theorem indexedSegments_length (drawing : PeriodicGridDrawing) :
    drawing.indexedSegments.length =
      (drawing.edgeRoutes.map fun route =>
        (gridPolylineSegments route).length).sum := by
  unfold indexedSegments
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_zipIdx]
  rw [show drawing.edgeRoutes.zipIdx.map (fun tagged =>
      (gridPolylineSegments tagged.1).length) =
    (drawing.edgeRoutes.zipIdx.map Prod.fst).map (fun route =>
      (gridPolylineSegments route).length) by
        rw [List.map_map]
        rfl]
  rw [List.zipIdx_map_fst]

end PeriodicGridDrawing
end LeanTrominoes

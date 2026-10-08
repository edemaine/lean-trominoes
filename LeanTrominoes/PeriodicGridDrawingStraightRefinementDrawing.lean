/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingStraightRefinementRoutes
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-! # The finite drawing assembled from the computed straight-edge routes -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

def straightRefinementDrawing {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := paddedGridSize drawing.gridSize - 1
  vertexPositions := drawing.vertexPositions.map (Cell.scale (paddedRefinementFactor drawing.gridSize))
  edgeRoutes := graph.edges.zipIdx.map (straightRefinementRoute graph drawing)

variable {Vertex : Type*} [DecidableEq Vertex]
  {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem straightRefinementDrawing_gridSize :
    (straightRefinementDrawing graph drawing).gridSize = paddedGridSize drawing.gridSize := by
  have positive := paddedGridSize_positive (by unfold gridSize; omega : 0 < drawing.gridSize)
  change paddedGridSize drawing.gridSize - 1 + 1 = paddedGridSize drawing.gridSize
  exact Nat.sub_add_cancel positive

theorem straightRefinementDrawing_gridSize_cubic :
    (straightRefinementDrawing graph drawing).gridSize ≤ 3300*drawing.gridSize^3 := by
  rw [straightRefinementDrawing_gridSize]
  exact paddedGridSize_cubic (Nat.zero_lt_succ drawing.gridSizePred)

theorem straightRefinementDrawing_vertexPosition (vertex : Vertex) :
    (straightRefinementDrawing graph drawing).vertexPosition graph vertex =
      Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph vertex) := by
  unfold vertexPosition
  change (drawing.vertexPositions.map (Cell.scale (paddedRefinementFactor drawing.gridSize))).getD
    (graph.vertices.idxOf vertex) (Cell.scale (paddedRefinementFactor drawing.gridSize) (0,0)) = _
  exact List.getD_map drawing.vertexPositions (0,0) (Cell.scale (paddedRefinementFactor drawing.gridSize))

theorem straightRefinementDrawing_edgeRoute {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) :
    (straightRefinementDrawing graph drawing).edgeRoute tagged.2 = straightRefinementRoute graph drawing tagged := by
  have originalAt := List.mem_zipIdx_iff_getElem?.mp member
  have taggedAt : graph.edges.zipIdx[tagged.2]? = some tagged := by
    rw [List.getElem?_zipIdx,originalAt]
    simp
  unfold edgeRoute
  change (graph.edges.zipIdx.map (straightRefinementRoute graph drawing)).getD tagged.2 [] = _
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,taggedAt,Option.map_some,Option.getD_some]

theorem straightRefinementDrawing_compatible
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).IsCompatible graph := by
  have scaled := isCompatible_scale (paddedRefinementFactor_positive drawing.gridSize) graph drawing planar.1.1
  have sameSize : (straightRefinementDrawing graph drawing).gridSize =
      (drawing.scale (paddedRefinementFactor drawing.gridSize)).gridSize := by
    rw [straightRefinementDrawing_gridSize,gridSize_scale (paddedRefinementFactor_positive drawing.gridSize)]
    rfl
  refine ⟨scaled.1,scaled.2.1,?_,scaled.2.2.2.1,?_,?_⟩
  · simp [straightRefinementDrawing]
  · intro position member
    have bounds := scaled.2.2.2.2.1 position member
    simpa only [PositionInFundamentalSquare,sameSize] using bounds
  · intro tagged member
    rw [straightRefinementDrawing_edgeRoute member,straightRefinementDrawing_vertexPosition,
      straightRefinementDrawing_vertexPosition,periodTranslation,straightRefinementDrawing_gridSize]
    have ends := straightRefinementRoute_endpoints planar degree graphLocal straight member
    exact ⟨ends.1,by simpa only [Cell.add,Int.add_comm] using ends.2⟩

theorem straightRefinementDrawing_routes_simple
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).RealRoutesAreSimple := by
  intro route member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  exact (straightRefinementRoute_valid planar degree graphLocal straight taggedMember).1.isRealSimple

theorem straightRefinementDrawing_orthogonal
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    (straightRefinementDrawing graph drawing).IsOrthogonal := by
  apply (isOrthogonal_iff_routes _).mpr
  intro route member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  exact (straightRefinementRoute_valid planar degree graphLocal straight taggedMember).2

end LeanTrominoes.PeriodicGridDrawing

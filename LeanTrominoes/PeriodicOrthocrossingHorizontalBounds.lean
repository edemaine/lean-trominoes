/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraphHorizontal
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Vertical bounds for horizontal orthocrossing drawings

If every local graph edge has zero vertical lattice offset, the canonical
track drawing never leaves its fundamental vertical band.  This is the first
geometric step toward exposing a blank vertical seam in the strip reduction.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Every explicitly stored route point lies strictly between the bottom and
top of the drawing's fundamental vertical band. -/
def RoutePointsInOpenVerticalBand (drawing : PeriodicGridDrawing) : Prop :=
  ∀ route ∈ drawing.edgeRoutes, ∀ point ∈ route,
    0 < point.2 ∧ point.2 < drawing.gridSize

end PeriodicGridDrawing

namespace PeriodicOrthocrossing

/-- The four rows used by one horizontal track route are all strictly inside
the drawing period. -/
private theorem horizontalRouteOrdinate_bounds
    {period track ordinate : Int}
    (tracks : 3 < track ∧ track + 1 < period)
    (ordinateCases :
      ordinate = 2 ∨ ordinate = 3 ∨
        ordinate = track ∨ ordinate = track + 1) :
    0 < ordinate ∧ ordinate < period := by
  rcases ordinateCases with rfl | rfl | rfl | rfl <;> omega

/-- The canonical track drawing of a horizontal local graph stays strictly
inside its fundamental vertical band. -/
theorem drawing_routePointsInOpenVerticalBand
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets) :
    (drawing graph).RoutePointsInOpenVerticalBand := by
  intro route routeMember point pointMember
  simp only [drawing, constructedEdgeRoutes, List.mem_map] at routeMember
  obtain ⟨taggedEdge, taggedEdgeMember, rfl⟩ := routeMember
  have edgeMember : taggedEdge.1 ∈ graph.edges :=
    List.fst_mem_of_mem_zipIdx taggedEdgeMember
  have edgeLocal := isLocal taggedEdge.1 edgeMember
  have verticalZero := horizontal taggedEdge.1 edgeMember
  have tracks := edgeTrack_bounds graph taggedEdgeMember
  have pointVerticalMember :
      point.2 ∈
        (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2).map Prod.snd :=
    List.mem_map_of_mem pointMember
  rw [drawing_gridSize]
  rcases offset_eq_of_span_le_one taggedEdge.1 edgeLocal with
    offsetZero | offsetRight | offsetLeft | offsetUp | offsetDown
  · apply horizontalRouteOrdinate_bounds tracks
    simp [constructedEdgeRoute, edgeCore, joinPolylines,
      translatePolyline, fanout, offsetZero, Cell.add, Cell.scale]
      at pointVerticalMember
    split at pointVerticalMember <;> split at pointVerticalMember <;> aesop
  · apply horizontalRouteOrdinate_bounds tracks
    simp [constructedEdgeRoute, edgeCore, joinPolylines,
      translatePolyline, fanout, offsetRight, Cell.add, Cell.scale]
      at pointVerticalMember
    split at pointVerticalMember <;> split at pointVerticalMember <;>
      split at pointVerticalMember <;> aesop
  · apply horizontalRouteOrdinate_bounds tracks
    simp [constructedEdgeRoute, edgeCore, joinPolylines,
      translatePolyline, fanout, offsetLeft, Cell.add, Cell.scale]
      at pointVerticalMember
    split at pointVerticalMember <;> split at pointVerticalMember <;>
      split at pointVerticalMember <;> aesop
  · rw [offsetUp] at verticalZero
    simp at verticalZero
  · rw [offsetDown] at verticalZero
    simp at verticalZero

end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivisionVertices

/-! # Compatibility of the translated raw subdivision

Doubling and translating the half-open residue representatives gives strict
interior positions. This bookkeeping drawing supplies the existing port
assignment interface, while raw bend positions remain unchanged.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

theorem shifted_vertexPosition_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {vertex : Vertex V} (member : vertex ∈ (subdivisionGraph source drawing).vertices) :
    (shiftedDrawing source drawing).vertexPosition (subdivisionGraph source drawing) vertex =
      shiftedPosition source drawing vertex := by
  have valid := List.idxOf_lt_length_of_mem member
  unfold vertexPosition
  change ((subdivisionGraph source drawing).vertices.map (shiftedPosition source drawing)).getD
    ((subdivisionGraph source drawing).vertices.idxOf vertex) (0,0) = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,List.getElem_idxOf valid]

theorem shifted_edgeRoute_of_tagged {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (shiftedDrawing source drawing).edgeRoute tagged.2 = shiftedRoute source drawing tagged.1 := by
  have valid : tagged.2 < (subdivisionGraph source drawing).edges.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have lookup := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp member)).2
  unfold edgeRoute
  change ((subdivisionGraph source drawing).edges.map (shiftedRoute source drawing)).getD tagged.2 [] = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,lookup]

theorem shifted_routesMatch {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source) :
    (shiftedDrawing source drawing).RoutesMatch (subdivisionGraph source drawing) := by
  intro tagged member
  have vertices := (subdivisionGraph_wellFormed compatible.1 drawing).2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  rw [shifted_edgeRoute_of_tagged source drawing member]
  simp only [shiftedRoute,List.head?_cons,List.getLast?_cons_cons,List.getLast?_singleton,
    shifted_vertexPosition_eq source drawing vertices.1,shifted_vertexPosition_eq source drawing vertices.2,
    periodTranslation,shiftedDrawing_gridSize]
  simp

theorem shifted_compatible {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) :
    (shiftedDrawing source drawing).IsCompatible (subdivisionGraph source drawing) := by
  refine ⟨subdivisionGraph_wellFormed planar.1.1.1 drawing,List.length_map _,List.length_map _,
    shifted_vertexPositions_nodup planar,?_,shifted_routesMatch planar.1.1⟩
  intro point member
  obtain ⟨vertex,vertexMember,rfl⟩ := List.mem_map.mp member
  exact shiftedPosition_inside planar.1.1 vertex (fun original equal =>
    original_vertex_mem.mp (equal ▸ vertexMember))

theorem shifted_straight {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    ((shiftedDrawing source drawing).edgeRoute tagged.2).length = 2 := by
  rw [shifted_edgeRoute_of_tagged source drawing member]
  rfl

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionVertexUniqueness

/-! # Complete graph compatibility of the straight bend subdivision -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem subdivision_vertexPosition_eq {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) {vertex : Vertex V}
    (member : vertex ∈ (subdivisionGraph source drawing factor).vertices) :
    (subdivisionDrawing source drawing factor).vertexPosition (subdivisionGraph source drawing factor) vertex=
      position source drawing factor vertex := by
  have valid := List.idxOf_lt_length_of_mem member
  unfold vertexPosition
  change ((subdivisionGraph source drawing factor).vertices.map (position source drawing factor)).getD
    ((subdivisionGraph source drawing factor).vertices.idxOf vertex) (0,0)=_
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,List.getElem_idxOf valid]

theorem subdivision_edgeRoute_of_tagged {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing factor).edges.zipIdx) :
    (subdivisionDrawing source drawing factor).edgeRoute tagged.2=straightRoute source drawing factor tagged.1 := by
  have valid : tagged.2 < (subdivisionGraph source drawing factor).edges.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have lookup := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp member)).2
  unfold edgeRoute
  change ((subdivisionGraph source drawing factor).edges.map (straightRoute source drawing factor)).getD tagged.2 []=_
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,lookup]

theorem subdivision_routesMatch {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source) {factor : Nat} (positive : 0 < factor) :
    (subdivisionDrawing source drawing factor).RoutesMatch (subdivisionGraph source drawing factor) := by
  intro tagged member
  have vertices := (subdivisionGraph_wellFormed compatible.1 drawing factor).2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  rw [subdivision_edgeRoute_of_tagged source drawing factor member]
  simp only [straightRoute,List.head?_cons,List.getLast?_cons_cons,List.getLast?_singleton,
    subdivision_vertexPosition_eq source drawing factor vertices.1,
    subdivision_vertexPosition_eq source drawing factor vertices.2,periodTranslation,
    subdivisionDrawing_gridSize source drawing positive]
  simp

theorem subdivision_compatible {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int)) :
    (subdivisionDrawing source drawing factor).IsCompatible (subdivisionGraph source drawing factor) := by
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0 < factor := by omega
  refine ⟨subdivisionGraph_wellFormed planar.1.1.1 drawing factor,?_,?_,
    subdivision_vertexPositions_nodup planar localDrawing localGraph spacing,?_,subdivision_routesMatch planar.1.1 positive⟩
  · exact List.length_map _
  · exact List.length_map _
  · intro point member
    obtain ⟨vertex,vertexMember,rfl⟩ := List.mem_map.mp member
    exact position_inside planar.1.1 (by omega) vertexMember

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision

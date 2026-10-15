/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionMembership
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionSegments
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendPerturbation

/-! # Every inserted vertex is an interior representative of its moved bend -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def bendCopy {V : Type*} (drawing : PeriodicGridDrawing) (factor edgeIndex pointIndex : Nat) : Cell :=
  Cell.sub (0,0) (sourceCell (V := V) drawing factor (.bend edgeIndex pointIndex))

theorem moved_route_length (drawing : PeriodicGridDrawing) (factor index : Nat) :
    ((InteriorBends.perturbDrawing drawing factor).edgeRoute index).length=(drawing.edgeRoute index).length := by
  rw [InteriorBends.perturbDrawing_edgeRoute,List.length_map]

theorem bend_lifted_representative {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {factor edgeIndex pointIndex : Nat} (positive : 0 < factor)
    (valid : pointIndex+1 < (drawing.edgeRoute edgeIndex).length) :
    Cell.add ((InteriorBends.perturbDrawing drawing factor).periodTranslation
        (bendCopy (V := V) drawing factor edgeIndex pointIndex))
      (((InteriorBends.perturbDrawing drawing factor).edgeRoute edgeIndex)[pointIndex]'(by rw [moved_route_length]; omega))=
        position source drawing factor (.bend edgeIndex pointIndex) := by
  have lookup : (drawing.edgeRoute edgeIndex).getD pointIndex (0,0)=(drawing.edgeRoute edgeIndex)[pointIndex] :=
    List.getD_eq_getElem _ _ (by omega)
  simp only [InteriorBends.perturbDrawing_edgeRoute,List.getElem_map,periodTranslation,
    InteriorBends.perturbDrawing_gridSize drawing positive,Nat.cast_mul,bendCopy,sourceCell,position,lookup]
  rw [InteriorBends.point_decomposition]
  apply Prod.ext <;> simp only [Cell.add,Cell.sub,Cell.scale] <;> ring

theorem position_inside {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible source) {factor : Nat} (spacing : 2 < (factor:Int))
    {vertex : Vertex V} (member : vertex ∈ (subdivisionGraph source drawing factor).vertices) :
    (subdivisionDrawing source drawing factor).PositionInFundamentalSquare (position source drawing factor vertex) := by
  have positive : 0 < factor := by omega
  have intPositive : (0:Int) < factor := by omega
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  rw [PositionInFundamentalSquare,subdivisionDrawing_gridSize source drawing positive]
  simp only [Nat.cast_mul]
  cases vertex with
  | original vertex =>
      have listed := original_vertex_mem.mp member
      have bounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem listed)
      simp only [position,Cell.scale]
      unfold PositionInFundamentalSquare at bounds
      exact ⟨mul_pos intPositive bounds.1,mul_lt_mul_of_pos_left bounds.2.1 intPositive,
        mul_pos intPositive bounds.2.2.1,mul_lt_mul_of_pos_left bounds.2.2.2 intPositive⟩
  | bend edgeIndex pointIndex =>
      exact InteriorBends.representative_interior gridPositive spacing _

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision

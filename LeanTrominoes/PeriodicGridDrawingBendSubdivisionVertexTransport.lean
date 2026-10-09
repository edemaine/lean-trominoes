/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionOccurrenceTransport

/-! # Lifted subdivision vertices represent the corresponding moved route points -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem bend_lifted_representative_copy {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {factor edgeIndex pointIndex : Nat} (positive : 0 < factor)
    (valid : pointIndex+1 < (drawing.edgeRoute edgeIndex).length) (translate : Cell) :
    Cell.add ((InteriorBends.perturbDrawing drawing factor).periodTranslation
        (Cell.sub translate (sourceCell (V := V) drawing factor (.bend edgeIndex pointIndex))))
      (((InteriorBends.perturbDrawing drawing factor).edgeRoute edgeIndex)[pointIndex]'(by rw [moved_route_length]; omega))=
    Cell.add (position source drawing factor (.bend edgeIndex pointIndex))
      ((subdivisionDrawing source drawing factor).periodTranslation translate) := by
  have lookup : (drawing.edgeRoute edgeIndex).getD pointIndex (0,0)=(drawing.edgeRoute edgeIndex)[pointIndex] :=
    List.getD_eq_getElem _ _ (by omega)
  simp only [InteriorBends.perturbDrawing_edgeRoute,List.getElem_map,periodTranslation,
    InteriorBends.perturbDrawing_gridSize drawing positive,subdivisionDrawing_gridSize source drawing positive,
    Nat.cast_mul,sourceCell,position,lookup]
  rw [InteriorBends.point_decomposition]
  apply Prod.ext <;> simp only [Cell.add,Cell.sub,Cell.scale] <;> ring

theorem original_lifted_representative {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0 < factor) (vertex : V) (translate : Cell) :
    Cell.add (Cell.scale factor (drawing.vertexPosition source vertex))
      ((InteriorBends.perturbDrawing drawing factor).periodTranslation translate)=
    Cell.add (position source drawing factor (.original vertex))
      ((subdivisionDrawing source drawing factor).periodTranslation translate) := by
  simp only [position,periodTranslation,InteriorBends.perturbDrawing_gridSize drawing positive,
    subdivisionDrawing_gridSize source drawing positive]

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision

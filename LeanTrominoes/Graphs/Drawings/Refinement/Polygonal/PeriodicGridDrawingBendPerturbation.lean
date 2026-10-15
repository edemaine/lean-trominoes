/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendCellLocality
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.Common.Geometry.GridPolylineRealScaling

/-! # Moving bends inward while preserving original graph vertices and endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

def perturbDrawing (drawing : PeriodicGridDrawing) (factor : Nat) : PeriodicGridDrawing where
  gridSizePred := factor*drawing.gridSize-1
  vertexPositions := drawing.vertexPositions.map (Cell.scale factor)
  edgeRoutes := drawing.edgeRoutes.map (List.map (point drawing.gridSize factor))

theorem perturbDrawing_gridSize (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0<factor) :
    (perturbDrawing drawing factor).gridSize=factor*drawing.gridSize := by
  have productPositive : 0<factor*drawing.gridSize :=
    Nat.mul_pos positive (Nat.zero_lt_succ drawing.gridSizePred)
  change factor*drawing.gridSize-1+1=factor*drawing.gridSize
  omega

theorem perturbDrawing_edgeRoute (drawing : PeriodicGridDrawing) (factor index : Nat) :
    (perturbDrawing drawing factor).edgeRoute index=(drawing.edgeRoute index).map (point drawing.gridSize factor) := by
  simpa only [perturbDrawing,edgeRoute,List.map_nil] using
    (List.getD_map (l := drawing.edgeRoutes) (d := []) (n := index) (List.map (point drawing.gridSize factor)))

theorem perturbDrawing_vertexPosition {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (vertex : V) :
    (perturbDrawing drawing factor).vertexPosition source vertex=Cell.scale factor (drawing.vertexPosition source vertex) := by
  simpa only [perturbDrawing,vertexPosition,Cell.scale,mul_zero] using
    (List.getD_map (l := drawing.vertexPositions) (d := (0,0))
      (n := source.vertices.idxOf vertex) (Cell.scale factor))

theorem perturbDrawing_routesMatch {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source)
    {factor : Nat} (positive : 0<factor) : (perturbDrawing drawing factor).RoutesMatch source := by
  intro tagged member
  have endpoints := compatible.2.2.2.2.2 tagged member
  have vertices := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have sourceBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem vertices.1)
  have targetBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem vertices.2)
  rw [perturbDrawing_edgeRoute]
  constructor
  · rw [List.head?_map,endpoints.1]
    simp only [Option.map_some,perturbDrawing_vertexPosition,point_interior sourceBounds]
  · rw [List.getLast?_map,endpoints.2]
    simp only [Option.map_some,perturbDrawing_vertexPosition,periodTranslation,perturbDrawing_gridSize drawing positive,
      Nat.cast_mul]
    exact congrArg some (point_translated_interior targetBounds tagged.1.offset)

theorem perturbDrawing_compatible {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source)
    {factor : Nat} (positive : 0<factor) : (perturbDrawing drawing factor).IsCompatible source := by
  have intPositive : (0:Int)<factor := by exact_mod_cast positive
  refine ⟨compatible.1,?_,?_,?_,?_,perturbDrawing_routesMatch compatible positive⟩
  · simpa only [perturbDrawing,List.length_map] using compatible.2.1
  · simpa only [perturbDrawing,List.length_map] using compatible.2.2.1
  · exact compatible.2.2.2.1.map (Cell.scale_injective intPositive.ne')
  · intro moved member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    have bounds := compatible.2.2.2.2.1 original originalMember
    simp only [PositionInFundamentalSquare,perturbDrawing_gridSize drawing positive,Cell.scale,Nat.cast_mul]
    unfold PositionInFundamentalSquare at bounds
    constructor
    · exact mul_pos intPositive bounds.1
    constructor
    · exact mul_lt_mul_of_pos_left bounds.2.1 intPositive
    constructor
    · exact mul_pos intPositive bounds.2.2.1
    · exact mul_lt_mul_of_pos_left bounds.2.2.2 intPositive

end LeanTrominoes.PeriodicGridDrawing.InteriorBends

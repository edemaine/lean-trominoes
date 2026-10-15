/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealPointUniqueness
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointMap
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra

/-! # Internal bend occurrences are unique in a planar periodic drawing -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

private theorem route_mem_of_index {drawing : PeriodicGridDrawing} {index : Nat}
    (valid : index < drawing.edgeRoutes.length) : drawing.edgeRoute index ∈ drawing.edgeRoutes := by
  unfold edgeRoute
  rw [List.getD_eq_getElem _ _ valid]
  exact List.getElem_mem valid

theorem listed_route_point_contains (drawing : PeriodicGridDrawing) (index pointIndex : Nat)
    (valid : pointIndex+1 < (drawing.edgeRoute index).length) (translate : Cell) :
    GridPolyline.RealContains (drawing.realEdgeRoute index translate)
      (realCell (Cell.add (drawing.periodTranslation translate) (drawing.edgeRoute index)[pointIndex])) := by
  obtain ⟨segment,member,start,_⟩ := GridPolyline.indexed_segment_at_point valid
  have base : GridPolyline.RealContains (drawing.edgeRoute index) (realCell (drawing.edgeRoute index)[pointIndex]) :=
    ⟨segment,List.fst_mem_of_mem_zipIdx member,by rw [← start]; exact GridSegment.realContains_start segment⟩
  have lifted := (GridPolyline.realContains_translate (drawing.periodTranslation translate) _ _).mpr base
  simpa only [realEdgeRoute,translatePolyline,realCell,Cell.add,Int.cast_add] using lifted

theorem internal_route_point_not_endpoint {drawing : PeriodicGridDrawing} {index pointIndex : Nat}
    (simple : GridPolyline.IsRealSimple (drawing.edgeRoute index)) (positive : 0 < pointIndex)
    (valid : pointIndex+1 < (drawing.edgeRoute index).length) (translate : Cell) :
    ¬GridPolyline.RealIsEndpoint (drawing.realEdgeRoute index translate)
      (realCell (Cell.add (drawing.periodTranslation translate) (drawing.edgeRoute index)[pointIndex])) := by
  intro endpoint
  have injective : Function.Injective (Cell.add (drawing.periodTranslation translate)) := by
    intro first second equal
    have x := congrArg Prod.fst equal
    have y := congrArg Prod.snd equal
    exact Prod.ext (by simp only [Cell.add] at x; omega) (by simp only [Cell.add] at y; omega)
  have base := (GridPolyline.realIsEndpoint_map_at_cell_iff _ injective).mp endpoint
  exact simple.internal_point_not_endpoint positive valid base

theorem internal_route_point_avoids_vertex {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {index pointIndex : Nat} (indexValid : index < drawing.edgeRoutes.length)
    (positive : 0 < pointIndex) (pointValid : pointIndex+1 < (drawing.edgeRoute index).length)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (routeCell vertexCell : Cell) :
    Cell.add (drawing.periodTranslation routeCell) (drawing.edgeRoute index)[pointIndex] ≠
      Cell.add vertex (drawing.periodTranslation vertexCell) := by
  intro equal
  have contains := listed_route_point_contains drawing index pointIndex pointValid routeCell
  have atVertex : GridPolyline.RealContains (drawing.realEdgeRoute index routeCell)
      (realCell (Cell.add vertex (drawing.periodTranslation vertexCell))) := by rwa [equal] at contains
  have endpoint := planar.1.2.2 vertex vertexMember vertexCell routeCell index indexValid atVertex
  rw [← equal] at endpoint
  exact internal_route_point_not_endpoint (planar.1.2.1 _ (route_mem_of_index indexValid)) positive pointValid routeCell endpoint

theorem internal_route_point_occurrences_unique {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {firstIndex secondIndex firstPointIndex secondPointIndex : Nat}
    (firstIndexValid : firstIndex < drawing.edgeRoutes.length)
    (secondIndexValid : secondIndex < drawing.edgeRoutes.length)
    (firstPositive : 0 < firstPointIndex) (_secondPositive : 0 < secondPointIndex)
    (firstValid : firstPointIndex+1 < (drawing.edgeRoute firstIndex).length)
    (secondValid : secondPointIndex+1 < (drawing.edgeRoute secondIndex).length)
    (firstCell secondCell : Cell)
    (equal : Cell.add (drawing.periodTranslation firstCell) (drawing.edgeRoute firstIndex)[firstPointIndex]=
      Cell.add (drawing.periodTranslation secondCell) (drawing.edgeRoute secondIndex)[secondPointIndex]) :
    (firstIndex,firstPointIndex,firstCell)=(secondIndex,secondPointIndex,secondCell) := by
  by_cases same : (firstIndex,firstCell)=(secondIndex,secondCell)
  · have indexEq : firstIndex=secondIndex := congrArg Prod.fst same
    have cellEq : firstCell=secondCell := congrArg Prod.snd same
    subst secondIndex secondCell
    have pointsEqual : (drawing.edgeRoute firstIndex)[firstPointIndex]=(drawing.edgeRoute firstIndex)[secondPointIndex] := by
      have x := congrArg Prod.fst equal
      have y := congrArg Prod.snd equal
      exact Prod.ext (by simp only [Cell.add] at x; omega) (by simp only [Cell.add] at y; omega)
    have pointEq := (planar.1.2.1 _ (route_mem_of_index firstIndexValid)).point_indices_eq firstValid secondValid pointsEqual
    rw [pointEq]
  · have firstContains := listed_route_point_contains drawing firstIndex firstPointIndex firstValid firstCell
    have secondContains := listed_route_point_contains drawing secondIndex secondPointIndex secondValid secondCell
    rw [← equal] at secondContains
    have endpoints := planar.2 firstIndex secondIndex firstCell secondCell firstIndexValid secondIndexValid same _
      firstContains secondContains
    exact (internal_route_point_not_endpoint (planar.1.2.1 _ (route_mem_of_index firstIndexValid))
      firstPositive firstValid firstCell endpoints.1).elim

end LeanTrominoes.PeriodicGridDrawing

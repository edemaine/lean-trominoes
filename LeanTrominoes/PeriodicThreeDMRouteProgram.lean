/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMPlanarQueries
import LeanTrominoes.PeriodicThreeDMRouteIndexSemantics
import LeanTrominoes.NativeDrawingRouteEndpoints

/-! # Native linear-space checking of 3DM incidence-route endpoints -/
namespace LeanTrominoes.PeriodicThreeDM.RouteProgram
open Gadget NormalizationCompiler BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open PeriodicGridDrawing PeriodicGridDrawing.NativeRoutes PlanarQueries

def body (color : WireColor) : Expr :=
  endpoints (var 0+1) (vertex 2 (var 1))
    (pointAdd (vertex 2 (targetIndex 2 (var 1) color)) (pointScale (var 3) (offsetPoint 2 (var 1) color)))

theorem body_noPower (color : WireColor) : (body color).noPower=true := by
  cases color <;> decide

def routeIndex (color : WireColor) : Expr := 3*var 0+.literal (FieldQueries.colorIndex color)

def oneColor (color : WireColor) : NativeScalar.Program :=
  NativeScalar.all (NativeScalar.arithmetic (problemField 0 3) (by decide))
    (NativeScalar.bind (cursor 2 (routeIndex color) (by cases color <;> decide))
      (NativeScalar.arithmetic (body color) (body_noPower color)))

theorem body_truth (input : Input) (wf : input.problem.IsWellFormed)
    (vertices : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length)
    (routes : input.drawing.edgeRoutes.length=input.problem.incidenceGraph.edges.length)
    (i : Nat) (hi : i < input.problem.triples.length) (color : WireColor) :
    let front := [i,(Arithmetic.fields input.drawing).length]
    let pos := address input.drawing front (3*i+FieldQueries.colorIndex color)
    (body color).Truth (pos::i::FlatEncoding.Planar.fields input) ↔
      IndexedRouteMatch input.problem input.drawing i color := by
  let d := input.drawing
  let k := 3*i+FieldQueries.colorIndex color
  let front := [i,(Arithmetic.fields d).length]
  let pos := address d front k
  let values := pos::i::FlatEncoding.Planar.fields input
  have hk : k<d.edgeRoutes.length := by rw [routes]; exact edgeIndex_lt input.problem i hi color
  have layout := selected_route_layout d front (FlatEncoding.fields input.problem) k hk [pos]
  have addr : (var 0+1).eval values=([pos]++Arithmetic.routeFront d front++
      (d.edgeRoutes.take k).flatMap Arithmetic.routeFields).length := by
    simp [values,pos,address,Expr.eval,Op.eval]
  have ep := endpoints_truth values _ _ d.edgeRoutes[k] layout (var 0+1)
    (vertex 2 (var 1)) (pointAdd (vertex 2 (targetIndex 2 (var 1) color))
      (pointScale (var 3) (offsetPoint 2 (var 1) color))) addr
  have sourceBound : i<d.vertexPositions.length := by
    rw [vertices,incidence_vertices_length]; omega
  have targetBound : input.problem.elementVertexIndex color (input.problem.triples[i].reference color).atom <
      d.vertexPositions.length := by
    rw [vertices]
    exact elementVertexIndex_lt input.problem color _ (wf _ (List.getElem_mem hi) color)
  have source := vertex_eval input [pos,i] (var 1) i rfl sourceBound
  have target := vertex_eval input [pos,i] (targetIndex 2 (var 1) color) _
    (targetIndex_eval input [pos,i] (var 1) color i rfl hi) targetBound
  have offset := offsetPoint_eval input [pos,i] (var 1) color i rfl hi
  have period := drawing_period input [pos,i]
  change (body color).Truth values ↔ _
  change (endpoints _ _ _).Truth values ↔ _
  rw [ep]
  change _ = _ ∧ _ = _ ↔ _
  dsimp only [values]
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,List.cons_append,List.nil_append] at source target offset period
  simp only [pointAdd_eval,pointScale_eval,source,target,offset,period]
  simp only [IndexedRouteMatch,edgeRoute,List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hk,List.getD_eq_getElem _ _ sourceBound,List.getD_eq_getElem _ _ targetBound,
    periodTranslation,d,k]

theorem oneColor_truth (input : Input) (wf : input.problem.IsWellFormed)
    (vertices : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length)
    (routes : input.drawing.edgeRoutes.length=input.problem.incidenceGraph.edges.length) (color : WireColor) :
    (oneColor color).value (FlatEncoding.Planar.fields input) ≠ 0 ↔
      ∀ i < input.problem.triples.length, IndexedRouteMatch input.problem input.drawing i color := by
  rw [oneColor,NativeScalar.all_value_ne_zero]
  have count := header_eval input [] 3
  change (problemField 0 3).eval (FlatEncoding.Planar.fields input)=input.problem.triples.length at count
  change (∀ i < (problemField 0 3).eval (FlatEncoding.Planar.fields input), _) ↔ _
  rw [count]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have hk : 3*i+FieldQueries.colorIndex color ≤ input.drawing.edgeRoutes.length := by
    rw [routes]; exact Nat.le_of_lt (edgeIndex_lt input.problem i hi color)
  have cur := cursor_value input.drawing [i,(Arithmetic.fields input.drawing).length]
    (FlatEncoding.fields input.problem) (routeIndex color) (by cases color <;> decide)
    (3*i+FieldQueries.colorIndex color) rfl hk
  change (cursor 2 (routeIndex color) _).value (i::FlatEncoding.Planar.fields input)=_ at cur
  change (body color).Truth ((cursor 2 (routeIndex color) _).value (i::FlatEncoding.Planar.fields input)::
    i::FlatEncoding.Planar.fields input) ↔ _
  rw [cur]
  exact body_truth input wf vertices routes i hi color

end LeanTrominoes.PeriodicThreeDM.RouteProgram

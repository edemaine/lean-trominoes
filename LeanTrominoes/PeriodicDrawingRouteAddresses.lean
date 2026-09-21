/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingRouteCursorSemantics

/-! # The route cursor locates each route in the stored trailer -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open NativeRouteCursor

theorem advance_take_routes (routes : List (List Cell)) (front rest : List Nat)
    (i : Nat) (hi : i≤routes.length) :
    advance (front++routes.flatMap routeFields++rest) i front.length =
      (front++(routes.take i).flatMap routeFields).length := by
  have h := advance_routes (routes.take i) front ((routes.drop i).flatMap routeFields++rest)
  have split : (routes.take i).flatMap routeFields++(routes.drop i).flatMap routeFields = routes.flatMap routeFields := by
    rw [← List.flatMap_append,List.take_append_drop]
  simpa only [List.length_take,Nat.min_eq_left hi,List.append_assoc,← split] using h

def routeFront (d : PeriodicGridDrawing) (front : List Nat) : List Nat :=
  front ++ [d.gridSize,FiniteBounds.radius d,d.indexedSegments.length,d.vertexPositions.length] ++
    d.indexedSegments.flatMap segmentFields ++ d.vertexPositions.flatMap pointFields ++ [d.edgeRoutes.length]

theorem routeFront_length (d : PeriodicGridDrawing) (front : List Nat) :
    (routeFront d front).length = front.length+5+6*d.indexedSegments.length+2*d.vertexPositions.length := by
  simp only [routeFront,List.length_append,List.length_cons,List.length_nil,segmentFields_length,pointFields_length]
  omega

theorem route_layout (d : PeriodicGridDrawing) (front rest : List Nat) :
    front++fields d++rest = routeFront d front ++ d.edgeRoutes.flatMap routeFields ++ rest := by
  simp [fields,trailer,routeFront,List.append_assoc]

theorem advance_drawing_routes (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (hi : i≤d.edgeRoutes.length) :
    advance (front++fields d++rest) i (front.length+5+6*d.indexedSegments.length+2*d.vertexPositions.length) =
      (routeFront d front++(d.edgeRoutes.take i).flatMap routeFields).length := by
  rw [route_layout,← routeFront_length]
  exact advance_take_routes _ _ _ i hi

theorem route_at_layout (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (hi : i<d.edgeRoutes.length) :
    front++fields d++rest =
      (routeFront d front++(d.edgeRoutes.take i).flatMap routeFields) ++ routeFields d.edgeRoutes[i] ++
        ((d.edgeRoutes.drop (i+1)).flatMap routeFields++rest) := by
  rw [route_layout]
  have split := List.take_append_drop i d.edgeRoutes
  rw [List.drop_eq_getElem_cons hi] at split
  have mapped := congrArg (List.flatMap routeFields) split
  simp only [List.flatMap_append,List.flatMap_cons] at mapped
  rw [← mapped]
  simp only [List.append_assoc]

end LeanTrominoes.PeriodicGridDrawing.Arithmetic

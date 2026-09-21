/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeRouteCursor
import LeanTrominoes.PeriodicDrawingArithmeticRouteCount

/-! # Route cursor and point-address semantics for the lossless trailer -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open NativeRouteCursor

theorem routeFields_length (points : List Cell) : (routeFields points).length = 1+2*points.length := by
  simp only [routeFields,List.length_cons,pointFields_length,Nat.add_comm]

theorem next_route (front rest : List Nat) (points : List Cell) :
    next (front ++ routeFields points ++ rest) front.length = (front ++ routeFields points).length := by
  simp only [next,List.append_assoc,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
    routeFields,List.cons_append,List.getElem?_cons_zero,Option.getD_some,List.length_append,
    List.length_cons,pointFields_length]
  omega

theorem advance_routes (routes : List (List Cell)) (front rest : List Nat) :
    advance (front ++ routes.flatMap routeFields ++ rest) routes.length front.length =
      (front ++ routes.flatMap routeFields).length := by
  induction routes generalizing front with
  | nil => simp [advance]
  | cons route routes ih =>
    simp only [List.length_cons,List.flatMap_cons,advance,Function.iterate_succ_apply]
    have current : front ++ (routeFields route ++ routes.flatMap routeFields) ++ rest =
        front ++ routeFields route ++ (routes.flatMap routeFields ++ rest) := by simp [List.append_assoc]
    rw [current,next_route]
    have tail := ih (front++routeFields route)
    simpa only [advance,List.append_assoc] using tail

theorem route_point_field (front rest : List Nat) (points : List Cell)
    (i : Nat) (axis : Fin 2) (hi : i<points.length) :
    (front ++ routeFields points ++ rest)[front.length+1+2*i+axis.val]?.getD 0 =
      (pointFields points[i])[axis.val]?.getD 0 := by
  rw [List.append_assoc,List.getElem?_append_right (by omega)]
  have offset : front.length+1+2*i+axis.val-front.length = (2*i+axis.val)+1 := by omega
  rw [offset]
  simp only [routeFields,List.cons_append,List.getElem?_cons_succ]
  clear offset
  induction points generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => fin_cases axis <;> simp [pointFields]
    | succ i =>
      have recursive := ih i (by simpa using hi)
      have offset : 2*(i+1)+axis.val = (2*i+axis.val)+1+1 := by omega
      simpa [pointFields,offset] using recursive

end LeanTrominoes.PeriodicGridDrawing.Arithmetic

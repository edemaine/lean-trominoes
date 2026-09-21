/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteGeometry

/-! # Reading stored route points, including singleton routes -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open PeriodicGridDrawing.Arithmetic

theorem route_length_field (front rest : List Nat) (points : List Cell) :
    (front++routeFields points++rest)[front.length]?.getD 0 = points.length := by
  rw [List.append_assoc,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  simp [routeFields]

theorem pointAt_eval (front rest : List Nat) (points : List Cell) (i : Nat) (hi : i<points.length)
    (address : Expr) (ha : address.eval (front++routeFields points++rest)=front.length+1+2*i) :
    pointEval (pointAt address) (front++routeFields points++rest) = points[i] := by
  have hx : (Expr.load address).eval (front++routeFields points++rest) = Encodable.encode points[i].1 := by
    simp only [Expr.eval,ha]
    simpa [pointFields] using route_point_field front rest points i ⟨0,by decide⟩ hi
  have hy : (Expr.load (address+1)).eval (front++routeFields points++rest) = Encodable.encode points[i].2 := by
    simp only [Expr.eval,Op.eval,ha]
    simpa [pointFields] using route_point_field front rest points i ⟨1,by decide⟩ hi
  simp only [pointAt,pointEval,fromCode_eval _ _ _ hx,fromCode_eval _ _ _ hy]

theorem route_point_queries (front rest : List Nat) (points : List Cell) (hn : 0<points.length)
    (route : Expr) (hr : route.eval (front++routeFields points++rest)=front.length) :
    pointEval (pointAt (route+1)) (front++routeFields points++rest) = points[0] ∧
    pointEval (pointAt (route+1+2*(.load route-1))) (front++routeFields points++rest) =
      points[points.length-1]'(by omega) := by
  constructor
  · apply pointAt_eval front rest points 0 hn
    simp only [eval_add,hr]
    rfl
  · apply pointAt_eval front rest points (points.length-1) (by omega)
    have size : (Expr.load route).eval (front++routeFields points++rest)=points.length := by
      simp only [Expr.eval,hr,route_length_field]
    simp only [eval_add,eval_mul,eval_sub,hr,size]
    rfl

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram

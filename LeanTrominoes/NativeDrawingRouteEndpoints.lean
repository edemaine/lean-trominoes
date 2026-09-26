/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeDrawingRoutePointFields

/-! # Checking route endpoints directly in the binary route stream -/
namespace LeanTrominoes.PeriodicGridDrawing.NativeRoutes
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry Arithmetic

def endpoints (header : Expr) (source target : Point) : Expr :=
  andE (ltE 0 (.load header))
    (andE (pointEqual (pointAt (header+1+2*0)) source)
      (pointEqual (pointAt (header+1+2*(.load header-1))) target))

theorem endpoints_truth (values storedFront storedRest : List Nat) (points : List Cell)
    (layout : values=storedFront++routeFields points++storedRest)
    (header : Expr) (source target : Point)
    (address : header.eval values=storedFront.length) :
    (endpoints header source target).Truth values ↔
      points.head?=some (pointEval source values) ∧ points.getLast?=some (pointEval target values) := by
  have size := length_query values storedFront storedRest points layout header address
  simp only [endpoints,truth_and,truth_lt,show (0:Expr).eval values=0 from rfl,size,pointEqual_truth]
  by_cases nonempty : 0<points.length
  · have first := point_query values storedFront storedRest points layout header 0 address 0 rfl nonempty
    have last := point_query values storedFront storedRest points layout header (.load header-1)
      address (points.length-1) (by simp only [eval_sub,size,show (1:Expr).eval values=1 from rfl]) (by omega)
    simp only [nonempty,true_and,first,last,List.head?_eq_getElem?,List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem nonempty,List.getElem?_eq_getElem (by omega : points.length-1<points.length),Option.some.injEq]
  · have empty : points=[] := List.length_eq_zero_iff.mp (by omega)
    simp [nonempty,empty]

end LeanTrominoes.PeriodicGridDrawing.NativeRoutes

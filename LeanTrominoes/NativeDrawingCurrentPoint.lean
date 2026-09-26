/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeDrawingRoutePointFields

/-! # Route-point queries survive additional local bindings -/
namespace LeanTrominoes.PeriodicGridDrawing.NativeRoutes
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry Arithmetic

def currentHeader (extra : Nat) : Expr := var (extra+1)+.literal (extra+2)
def currentPoint (extra : Nat) : Point := pointAt (currentHeader extra+1+2*var extra)
def currentLength (extra : Nat) : Expr := .load (currentHeader extra)

def pointContext (d : PeriodicGridDrawing) (front : List Nat) (i j : Nat) : List Nat :=
  j :: address d (i::front) i :: i :: front

theorem current_queries (d : PeriodicGridDrawing) (front rest extra : List Nat)
    (i : Nat) (hi : i<d.edgeRoutes.length) (j : Nat) (hj : j<d.edgeRoutes[i].length) :
    pointEval (currentPoint extra.length) (extra++pointContext d front i j++fields d++rest) = d.edgeRoutes[i][j] ∧
    (currentLength extra.length).eval (extra++pointContext d front i j++fields d++rest) = d.edgeRoutes[i].length := by
  let a := address d (i::front) i
  let leading := extra++[j,a]
  let before := leading++routeFront d (i::front)++(d.edgeRoutes.take i).flatMap routeFields
  let after := (d.edgeRoutes.drop (i+1)).flatMap routeFields++rest
  let values := extra++pointContext d front i j++fields d++rest
  have layout : values = before++routeFields d.edgeRoutes[i]++after := by
    have h := selected_route_layout d (i::front) rest i hi leading
    simpa only [values,before,after,leading,pointContext,List.append_assoc,List.cons_append,List.nil_append,a] using h
  have length : before.length = extra.length+a+2 := by
    simp only [before,leading,List.length_append,List.length_cons,List.length_nil,a,address]
    omega
  have header : (currentHeader extra.length).eval values = before.length := by
    rw [length]
    change (extra++pointContext d front i j++fields d++rest)[extra.length+1]?.getD 0+(extra.length+2)=_
    simp only [List.append_assoc,List.getElem?_append_right (by omega : extra.length ≤ extra.length+1),
      Nat.add_sub_cancel_left,pointContext,List.cons_append,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
    omega
  have index : (var extra.length).eval values = j := by
    change (extra++pointContext d front i j++fields d++rest)[extra.length]?.getD 0=j
    simp only [List.append_assoc,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
      pointContext,List.cons_append,List.getElem?_cons_zero,Option.getD_some]
  exact ⟨point_query values before after _ layout (currentHeader extra.length) (var extra.length) header j index hj,
    length_query values before after _ layout (currentHeader extra.length) header⟩

end LeanTrominoes.PeriodicGridDrawing.NativeRoutes

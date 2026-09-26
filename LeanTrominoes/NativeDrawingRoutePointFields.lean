/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeDrawingRouteQueries
import LeanTrominoes.BoundedArithmeticSignedResidue

/-! # Signed point queries at a cursor-selected route header -/
namespace LeanTrominoes.PeriodicGridDrawing.NativeRoutes
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry Arithmetic

def pointAt (address : Expr) : Point := (fromCode (.load address),fromCode (.load (address+1)))

theorem length_query (values storedFront storedRest : List Nat) (points : List Cell)
    (layout : values=storedFront++routeFields points++storedRest) (header : Expr)
    (address : header.eval values=storedFront.length) : (.load header : Expr).eval values=points.length := by
  rw [Expr.eval,address,layout,List.append_assoc,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  simp [routeFields]

theorem point_query (values storedFront storedRest : List Nat) (points : List Cell)
    (layout : values=storedFront++routeFields points++storedRest) (header index : Expr)
    (address : header.eval values=storedFront.length) (i : Nat) (he : index.eval values=i)
    (hi : i<points.length) : pointEval (pointAt (header+1+2*index)) values=points[i] := by
  have coordinate (axis : Fin 2) :
      (.load (header+1+2*index+.literal axis.val) : Expr).eval values =
        (pointFields points[i])[axis.val]?.getD 0 := by
    change values[header.eval values+1+2*index.eval values+axis.val]?.getD 0 = _
    rw [address,he,layout]
    exact route_point_field storedFront storedRest points i axis hi
  have x := coordinate 0
  have y := coordinate 1
  have hx : (.load (header+1+2*index) : Expr).eval values=Encodable.encode points[i].1 := by
    simpa only [pointFields,Fin.val_zero,List.getElem?_cons_zero,Option.getD_some,
      Expr.eval,Op.eval,Nat.add_zero] using x
  have hy : (.load (header+1+2*index+1) : Expr).eval values=Encodable.encode points[i].2 := by
    simpa only [pointFields,Fin.val_one,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Expr.eval,Op.eval] using y
  exact Prod.ext (fromCode_eval _ _ _ hx) (fromCode_eval _ _ _ hy)

theorem selected_route_layout (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (hi : i<d.edgeRoutes.length) (extra : List Nat) :
    extra++front++fields d++rest =
      (extra++routeFront d front++(d.edgeRoutes.take i).flatMap routeFields) ++ routeFields d.edgeRoutes[i] ++
        ((d.edgeRoutes.drop (i+1)).flatMap routeFields++rest) := by
  have h := route_at_layout d front rest i hi
  simpa only [List.append_assoc] using congrArg (extra++·) h

end LeanTrominoes.PeriodicGridDrawing.NativeRoutes

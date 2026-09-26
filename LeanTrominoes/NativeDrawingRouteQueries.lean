/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeScalarAdapters
import LeanTrominoes.PeriodicDrawingRouteAddresses
import LeanTrominoes.PeriodicDrawingArithmeticSuffix

/-! # Linear-space enumeration of stored drawing routes and points -/
namespace LeanTrominoes.PeriodicGridDrawing.NativeRoutes
open BoundedArithmetic BoundedArithmetic.Expr Arithmetic

private def arithmetic (expr : Expr) (h : expr.noPower=true) := NativeScalar.arithmetic expr h

def routeStart (depth : Nat) : Expr := .literal (depth+5)+6*var (depth+2)+2*var (depth+3)
def routeCount (depth : Nat) : Expr := .load (routeStart depth-1)

theorem routeStart_noPower (depth : Nat) : (routeStart depth).noPower=true := by simp [routeStart,Expr.noPower]
theorem routeCount_noPower (depth : Nat) : (routeCount depth).noPower=true := by
  simp [routeCount,Expr.noPower,routeStart_noPower]

theorem routeStart_eval (d : PeriodicGridDrawing) (front rest : List Nat) :
    (routeStart front.length).eval (front++fields d++rest) =
      front.length+5+6*d.indexedSegments.length+2*d.vertexPositions.length := by
  have segments := header_get_suffix d front rest 2 (by decide)
  have vertices := header_get_suffix d front rest 3 (by decide)
  change (var (front.length+2)).eval (front++fields d++rest) = d.indexedSegments.length at segments
  change (var (front.length+3)).eval (front++fields d++rest) = d.vertexPositions.length at vertices
  simp only [routeStart,eval_add,eval_mul,eval_literal,segments,vertices]
  rfl

theorem routeCount_eval (d : PeriodicGridDrawing) (front rest : List Nat) :
    (routeCount front.length).eval (front++fields d++rest) = d.edgeRoutes.length := by
  rw [routeCount,Expr.eval,eval_sub,routeStart_eval]
  have address : front.length+5+6*d.indexedSegments.length+2*d.vertexPositions.length-1 =
      front.length+4+6*d.indexedSegments.length+2*d.vertexPositions.length := by omega
  rw [show (1:Expr).eval (front++fields d++rest)=1 from rfl,address]
  simpa only [List.append_nil] using routeCount_field d front rest

def cursor (depth : Nat) (index : Expr) (allowed : index.noPower=true) : NativeScalar.Program :=
  NativeScalar.cursor (arithmetic index allowed) (arithmetic (routeStart depth) (routeStart_noPower depth))

def address (d : PeriodicGridDrawing) (front : List Nat) (i : Nat) : Nat :=
  (routeFront d front++(d.edgeRoutes.take i).flatMap routeFields).length

theorem cursor_value (d : PeriodicGridDrawing) (front rest : List Nat) (index : Expr)
    (allowed : index.noPower=true) (i : Nat) (he : index.eval (front++fields d++rest)=i) (hi : i≤d.edgeRoutes.length) :
    (cursor front.length index allowed).value (front++fields d++rest) = address d front i := by
  change NativeRouteCursor.advance (front++fields d++rest) (index.eval (front++fields d++rest))
    ((routeStart front.length).eval (front++fields d++rest)) = _
  rw [he,routeStart_eval]
  simpa only [List.append_nil,address] using advance_drawing_routes d front rest i hi

def allRoutes (depth : Nat) (body : NativeScalar.Program) : NativeScalar.Program :=
  NativeScalar.all (arithmetic (routeCount depth) (routeCount_noPower depth))
    (NativeScalar.bind (cursor (depth+1) (var 0) (by rfl)) body)

theorem allRoutes_truth (d : PeriodicGridDrawing) (front rest : List Nat) (body : NativeScalar.Program) :
    (allRoutes front.length body).value (front++fields d++rest) ≠ 0 ↔
      ∀ i < d.edgeRoutes.length, body.value (address d (i::front) i :: i :: (front++fields d++rest)) ≠ 0 := by
  rw [allRoutes,NativeScalar.all_value_ne_zero]
  change (∀ i < (routeCount front.length).eval (front++fields d++rest),
    body.value ((cursor (front.length+1) (var 0) _).value (i::(front++fields d++rest)) :: i :: (front++fields d++rest)) ≠ 0) ↔ _
  rw [routeCount_eval]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have h := cursor_value d (i::front) rest (var 0) (by rfl) i rfl (Nat.le_of_lt hi)
  change (cursor (front.length+1) (var 0) _).value (i::(front++fields d++rest)) = address d (i::front) i at h
  rw [h]

theorem route_length_at (d : PeriodicGridDrawing) (front rest : List Nat) (i : Nat) (hi : i<d.edgeRoutes.length) :
    (front++fields d++rest)[address d front i]?.getD 0 = d.edgeRoutes[i].length := by
  have layout := route_at_layout d front rest i hi
  rw [layout]
  unfold address
  rw [List.append_assoc,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  simp [routeFields]

def allPoints (depth : Nat) (body : NativeScalar.Program) : NativeScalar.Program :=
  allRoutes depth (NativeScalar.all (arithmetic (.load (var 0+1)) (by decide)) body)

theorem allPoints_truth (d : PeriodicGridDrawing) (front rest : List Nat) (body : NativeScalar.Program) :
    (allPoints front.length body).value (front++fields d++rest) ≠ 0 ↔
      ∀ i (hi : i<d.edgeRoutes.length), ∀ j < d.edgeRoutes[i].length,
        body.value (j :: address d (i::front) i :: i :: (front++fields d++rest)) ≠ 0 := by
  rw [allPoints,allRoutes_truth]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [NativeScalar.all_value_ne_zero]
  have size := route_length_at d (i::front) rest i hi
  change (∀ j < (address d (i::front) i :: i :: (front++fields d++rest))[address d (i::front) i+1]?.getD 0,
    body.value (j :: address d (i::front) i :: i :: (front++fields d++rest)) ≠ 0) ↔ _
  simp only [List.getElem?_cons_succ]
  change (∀ j < ((i::front)++fields d++rest)[address d (i::front) i]?.getD 0, _) ↔ _
  rw [size]

end LeanTrominoes.PeriodicGridDrawing.NativeRoutes

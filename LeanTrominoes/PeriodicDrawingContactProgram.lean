/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NativeDrawingCurrentPoint
import LeanTrominoes.PeriodicDrawingRoutePointEnumeration

/-! # A linear-space program for every halo-relevant route-point contact -/
namespace LeanTrominoes.PeriodicGridDrawing.ContactProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry NativeRoutes Arithmetic

private def arithmetic (expr : Expr) (h : expr.noPower=true) := NativeScalar.arithmetic expr h

def endpoint (index size : Expr) : Expr := orE (eqE index 0) (eqE (index+1) size)

-- Local bindings: y, x, second point, second cursor, second route,
-- first point, first cursor, first route; then the caller's input.
def body (depth : Nat) : Expr :=
  orE (andE (eqE (var 7) (var 4)) (andE (eqE (var 5) (var 2))
    (andE (eqE (var 1) 2) (eqE (var 0) 2))))
    (orE (notE (pointEqual
      (pointAdd (currentPoint 5) (pointScale (var (depth+8)) (difference (var 1) 2,difference (var 0) 2)))
      (currentPoint 2)))
      (andE (endpoint (var 5) (currentLength 5)) (endpoint (var 2) (currentLength 2))))

theorem body_noPower (depth : Nat) : (body depth).noPower=true := by
  simp [body,endpoint,currentPoint,currentLength,currentHeader,pointAt,pointEqual,pointAdd,pointScale,
    fromCode,add,scale,equal,difference,orE,notE,eqE,andE,var,Expr.noPower]

def translations (depth : Nat) : NativeScalar.Program :=
  NativeScalar.all (arithmetic 5 (by rfl))
    (NativeScalar.all (arithmetic 5 (by rfl)) (arithmetic (body depth) (body_noPower depth)))

def program (depth : Nat) : NativeScalar.Program :=
  allPoints depth (allPoints (depth+3) (translations depth))

def Contact (d : PeriodicGridDrawing) (first second : IndexedRoutePoint) (relative : Cell) : Prop :=
  RoutePointOccurrenceKey first relative = RoutePointOccurrenceKey second (0,0) ∨
    Cell.add first.point (d.periodTranslation relative) ≠ second.point ∨
    (first.IsEndpoint ∧ second.IsEndpoint)

theorem body_truth (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (hi : i<d.edgeRoutes.length) (j : Nat) (hj : j<d.edgeRoutes[i].length)
    (k : Nat) (hk : k<d.edgeRoutes.length) (l : Nat) (hl : l<d.edgeRoutes[k].length) (x y : Nat) :
    (body front.length).Truth
      (y::x::pointContext d (pointContext d front i j) k l++fields d++rest) ↔
      Contact d (d.routePointAt i hi j hj) (d.routePointAt k hk l hl) ((x:Int)-2,(y:Int)-2) := by
  let first := pointContext d front i j
  let second := pointContext d first k l
  let extra := [y,x,l,address d (k::first) k,k]
  have one := current_queries d front rest extra i hi j hj
  have two := current_queries d first rest [y,x] k hk l hl
  change pointEval (currentPoint 5) (y::x::second++fields d++rest)=d.edgeRoutes[i][j] ∧
    (currentLength 5).eval (y::x::second++fields d++rest)=d.edgeRoutes[i].length at one
  change pointEval (currentPoint 2) (y::x::second++fields d++rest)=d.edgeRoutes[k][l] ∧
    (currentLength 2).eval (y::x::second++fields d++rest)=d.edgeRoutes[k].length at two
  have period : (var (front.length+8)).eval (y::x::second++fields d++rest)=d.gridSize := by
    have h := header_get_suffix d (y::x::second) rest 0 (by decide)
    have len : (y::x::second).length=front.length+8 := by simp [second,first,pointContext]
    simpa only [eval_var,len,Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h
  dsimp only [second,first] at one two period
  simp only [body,truth_or,truth_and,truth_eq,truth_not,pointEqual_truth,pointAdd_eval,pointScale_eval,
    one.1,one.2,two.1,two.2,period,endpoint]
  simp only [pointEval,difference_eval]
  change ((i=k ∧ j=l ∧ x=2 ∧ y=2) ∨
    Cell.add d.edgeRoutes[i][j] (Cell.scale d.gridSize ((x:Int)-2,(y:Int)-2)) ≠ d.edgeRoutes[k][l] ∨
      ((j=0 ∨ j+1=d.edgeRoutes[i].length) ∧ (l=0 ∨ l+1=d.edgeRoutes[k].length))) ↔ _
  simp only [Contact,routePointAt,RoutePointOccurrenceKey,IndexedRoutePoint.IsEndpoint,periodTranslation,
    Prod.mk.injEq,Prod.fst,Prod.snd]
  have hx : (x:Int)-2=0 ↔ x=2 := by omega
  have hy : (y:Int)-2=0 ↔ y=2 := by omega
  simp only [hx,hy]

end LeanTrominoes.PeriodicGridDrawing.ContactProgram

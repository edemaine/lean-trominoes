/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.NativeDrawingCurrentPoint
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicDrawingRoutePointEnumeration

/-! # Linear-space residue checks for arbitrary periodic route-point contacts -/
namespace LeanTrominoes.PeriodicGridDrawing.EndpointResidueProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry NativeRoutes Arithmetic

private def arithmetic (expr : Expr) (h : expr.noPower=true) := NativeScalar.arithmetic expr h

def endpoint (index size : Expr) : Expr := orE (eqE index 0) (eqE (index+1) size)

-- Bindings: second point, second cursor, second route, first point,
-- first cursor, first route; then the caller's input.
def body (depth : Nat) : Expr :=
  orE (andE (eqE (var 5) (var 2)) (eqE (var 3) (var 0)))
    (orE (notE (pointEqualModulo (var (depth+6)) (currentPoint 3) (currentPoint 0)))
      (andE (endpoint (var 3) (currentLength 3)) (endpoint (var 0) (currentLength 0))))

theorem body_noPower (depth : Nat) : (body depth).noPower=true := by
  simp [body,endpoint,currentPoint,currentLength,currentHeader,pointAt,pointEqualModulo,
    equalModulo,fromCode,orE,notE,eqE,andE,var,Expr.noPower]

def program (depth : Nat) : NativeScalar.Program :=
  allPoints depth (allPoints (depth+3) (arithmetic (body depth) (body_noPower depth)))

def Contact (d : PeriodicGridDrawing) (first second : IndexedRoutePoint) : Prop :=
  (first.routeIndex=second.routeIndex ∧ first.pointIndex=second.pointIndex) ∨
    (first.point.1 % (d.gridSize:Int),first.point.2 % (d.gridSize:Int)) ≠
      (second.point.1 % (d.gridSize:Int),second.point.2 % (d.gridSize:Int)) ∨
    (first.IsEndpoint ∧ second.IsEndpoint)

theorem body_truth (d : PeriodicGridDrawing) (front rest : List Nat)
    (i : Nat) (hi : i<d.edgeRoutes.length) (j : Nat) (hj : j<d.edgeRoutes[i].length)
    (k : Nat) (hk : k<d.edgeRoutes.length) (l : Nat) (hl : l<d.edgeRoutes[k].length) :
    (body front.length).Truth (pointContext d (pointContext d front i j) k l++fields d++rest) ↔
      Contact d (d.routePointAt i hi j hj) (d.routePointAt k hk l hl) := by
  let first := pointContext d front i j
  let second := pointContext d first k l
  let extra := [l,address d (k::first) k,k]
  have one := current_queries d front rest extra i hi j hj
  have two := current_queries d first rest [] k hk l hl
  change pointEval (currentPoint 3) (second++fields d++rest)=d.edgeRoutes[i][j] ∧
    (currentLength 3).eval (second++fields d++rest)=d.edgeRoutes[i].length at one
  change pointEval (currentPoint 0) (second++fields d++rest)=d.edgeRoutes[k][l] ∧
    (currentLength 0).eval (second++fields d++rest)=d.edgeRoutes[k].length at two
  have period : (var (front.length+6)).eval (second++fields d++rest)=d.gridSize := by
    have h := header_get_suffix d second rest 0 (by decide)
    have len : second.length=front.length+6 := by simp [second,first,pointContext]
    simpa only [eval_var,len,Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using h
  dsimp only [second,first] at one two period
  simp only [body,truth_or,truth_and,truth_eq,truth_not,pointEqualModulo_truth,
    one.1,one.2,two.1,two.2,period,endpoint]
  change ((i=k ∧ j=l) ∨ _ ∨ ((j=0 ∨ j+1=d.edgeRoutes[i].length) ∧
    (l=0 ∨ l+1=d.edgeRoutes[k].length))) ↔ _
  rfl

theorem program_indexed (d : PeriodicGridDrawing) (front rest : List Nat) :
    (program front.length).value (front++fields d++rest) ≠ 0 ↔
      ∀ i (hi : i<d.edgeRoutes.length), ∀ j (hj : j<d.edgeRoutes[i].length),
      ∀ k (hk : k<d.edgeRoutes.length), ∀ l (hl : l<d.edgeRoutes[k].length),
        Contact d (d.routePointAt i hi j hj) (d.routePointAt k hk l hl) := by
  rw [program,allPoints_truth]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  have inner := allPoints_truth d (pointContext d front i j) rest
    (arithmetic (body front.length) (body_noPower front.length))
  change ((allPoints (front.length+3) _).value
    (j::address d (i::front) i::i::(front++fields d++rest)) ≠ 0) ↔ _ at inner
  apply inner.trans
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  exact body_truth d front rest i hi j hj k hk l hl

theorem program_points (d : PeriodicGridDrawing) (front rest : List Nat) :
    (program front.length).value (front++fields d++rest) ≠ 0 ↔
      ∀ first ∈ d.indexedRoutePoints, ∀ second ∈ d.indexedRoutePoints, Contact d first second := by
  rw [program_indexed,forall_indexedRoutePoints_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  exact (forall_indexedRoutePoints_iff d _).symm

end LeanTrominoes.PeriodicGridDrawing.EndpointResidueProgram

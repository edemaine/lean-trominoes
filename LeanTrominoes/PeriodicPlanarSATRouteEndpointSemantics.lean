/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRoutePointSemantics
import LeanTrominoes.PeriodicPlanarSATRouteOffsetSemantics

/-! # Endpoint comparison agrees with the stored route endpoints -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open RouteInput PeriodicCNF.FlatScanner PeriodicGridDrawing.Arithmetic

theorem endpointExpr_truth (input : Input Nat) (front : List Nat)
    (route source target header literal : Expr) (storedFront storedRest : List Nat) (points : List Cell)
    (layout : front++context input = storedFront++routeFields points++storedRest)
    (hr : route.eval (front++context input)=storedFront.length)
    (s t h i : Nat) (c : PeriodicClause Nat)
    (hs : source.eval (front++context input)=s) (ht : target.eval (front++context input)=t)
    (hsv : s < input.2.vertexPositions.length) (htv : t < input.2.vertexPositions.length)
    (hc : (h,c)∈clauseEntries 1 input.1.clauses) (hi : i<c.length)
    (hh : header.eval (front++context input)=h) (hl : literal.eval (front++context input)=h+1+4*i) :
    (endpointExpr front.length route source target header literal).Truth (front++context input) ↔
      points.head? = some input.2.vertexPositions[s] ∧
      points.getLast? = some (Cell.add input.2.vertexPositions[t]
        (input.2.periodTranslation (Cell.sub c[i].offset (PeriodicCNF.clauseAnchor c)))) := by
  have size : (Expr.load route).eval (front++context input)=points.length := by
    rw [Expr.eval,hr,layout,route_length_field]
  have period : (var (front.length+6)).eval (front++context input)=input.2.gridSize := by
    simpa using drawing_header_eval input front ⟨0,by decide⟩
  rw [endpointExpr,truth_and,truth_lt,size]
  change (0 < points.length ∧ _) ↔ _
  by_cases hn : 0<points.length
  · have queries := route_point_queries storedFront storedRest points hn route (by rwa [← layout])
    rw [← layout] at queries
    have first : points.head? = some points[0] := by
      cases points with
      | nil => simp at hn
      | cons p ps => rfl
    have last : points.getLast? = some (points[points.length-1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega)]
    rw [truth_and,pointEqual_truth,pointEqual_truth,queries.1,queries.2,
      pointAdd_eval,pointScale_eval,
      RouteInput.vertex_eval input front source s hs hsv,
      RouteInput.vertex_eval input front target t ht htv,period,offset_eval input front literal header h c hc i hi hl hh,
      first,last]
    simp only [hn,true_and,Option.some.injEq]
    rfl
  · have empty : points=[] := List.length_eq_zero_iff.mp (by omega)
    simp [empty]

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteEndpointSemantics
import LeanTrominoes.PeriodicDrawingRouteAddresses

/-! # The cursor-and-endpoint leaf checks the selected stored route -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open RouteInput PeriodicCNF.FlatScanner PeriodicGridDrawing.Arithmetic PeriodicCNFFlatEncoding

theorem cursorQuery_value (input : Input Nat) (t r e k ci h v : Nat) (he : e ≤ input.2.edgeRoutes.length) :
    cursorQuery.value ([t,r,e,k,ci,h,v]++context input) =
      (routeFront input.2 (drawingFront input [t,r,e,k,ci,h,v])++
        (input.2.edgeRoutes.take e).flatMap routeFields).length := by
  change NativeRouteCursor.advance _ e ((routeStart 7).eval _) = _
  have start := routeStart_eval input [t,r,e,k,ci,h,v]
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at start
  rw [start,drawing_layout]
  have shape : 7+11+6*input.2.indexedSegments.length+2*input.2.vertexPositions.length =
      (drawingFront input [t,r,e,k,ci,h,v]).length+5+6*input.2.indexedSegments.length+2*input.2.vertexPositions.length := by
    rw [drawingFront_length]
    rfl
  rw [shape]
  exact advance_drawing_routes _ _ _ e he

theorem targetBody_truth (input : Input Nat) (t r e k ci h v : Nat)
    (he : e < input.2.edgeRoutes.length) (hs : v+ci < input.2.vertexPositions.length) (ht : t < input.2.vertexPositions.length)
    (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) (hk : k<c.length) :
    targetBody.value ([t,r,e,k,ci,h,v]++context input) ≠ 0 ↔
      input.2.edgeRoutes[e].head? = some input.2.vertexPositions[v+ci] ∧
      input.2.edgeRoutes[e].getLast? = some (Cell.add input.2.vertexPositions[t]
        (input.2.periodTranslation (Cell.sub c[k].offset (PeriodicCNF.clauseAnchor c)))) := by
  let cursor := cursorQuery.value ([t,r,e,k,ci,h,v]++context input)
  let leading := routeFront input.2 (drawingFront input [t,r,e,k,ci,h,v])++
    (input.2.edgeRoutes.take e).flatMap routeFields
  let rest := (input.2.edgeRoutes.drop (e+1)).flatMap routeFields++formulaFields input.1
  have cursorEq : cursor=leading.length := cursorQuery_value input t r e k ci h v (by omega)
  have layout : [cursor,t,r,e,k,ci,h,v]++context input =
      (cursor::leading)++routeFields input.2.edgeRoutes[e]++rest := by
    have old := drawing_layout input [t,r,e,k,ci,h,v]
    rw [route_at_layout input.2 _ _ e he] at old
    simpa only [List.cons_append,List.nil_append] using congrArg (List.cons cursor) old
  change (endpointExpr 8 (var 0+1) (var 7+var 5) (var 1) (var 6) (var 6+1+4*var 4)).Truth
    ([cursor,t,r,e,k,ci,h,v]++context input) ↔ _
  apply endpointExpr_truth input [cursor,t,r,e,k,ci,h,v]
    (var 0+1) (var 7+var 5) (var 1) (var 6) (var 6+1+4*var 4)
    (cursor::leading) rest input.2.edgeRoutes[e] layout
    (by simp only [eval_add,eval_var,List.cons_append,List.nil_append,List.getElem?_cons_zero,
          Option.getD_some,List.length_cons]; change cursor+1=leading.length+1; omega)
    (v+ci) t h k c (by rfl) (by rfl) hs ht hc hk (by rfl) (by rfl)

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram

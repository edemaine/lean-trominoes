/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteProgram
import LeanTrominoes.PeriodicDrawingArithmeticSuffix
import LeanTrominoes.PeriodicDrawingRouteCursorSemantics

/-! # Geometry access from the shared route-verification environment -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteInput
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open PeriodicCNFFlatEncoding PeriodicCNF.FlatScanner

def drawingFront (input : Input Nat) (front : List Nat) : List Nat :=
  front ++ [(formulaFields input.1).length,clauseMarks 1 input.1.clauses,
    literalMarks 1 input.1.clauses,0,0,(FlatEncoding.drawingFields input.2).length]

theorem drawingFront_length (input : Input Nat) (front : List Nat) :
    (drawingFront input front).length = front.length+6 := by simp [drawingFront]

theorem drawing_layout (input : Input Nat) (front : List Nat) :
    front++context input = drawingFront input front ++ PeriodicGridDrawing.Arithmetic.fields input.2 ++ formulaFields input.1 := by
  simp [drawingFront,context,FlatEncoding.fields,FlatEncoding.drawingFields,List.append_assoc]

theorem drawing_header_eval (input : Input Nat) (front : List Nat) (i : Fin 4) :
    (var (front.length+6+i.val)).eval (front++context input) =
      ([input.2.gridSize,PeriodicGridDrawing.FiniteBounds.radius input.2,
        input.2.indexedSegments.length,input.2.vertexPositions.length][i.val]?.getD 0) := by
  rw [eval_var,drawing_layout,← drawingFront_length]
  exact PeriodicGridDrawing.Arithmetic.header_get_suffix _ _ _ _ i.isLt

theorem vertex_eval (input : Input Nat) (front : List Nat) (index : Expr)
    (i : Nat) (he : index.eval (front++context input)=i) (hi : i < input.2.vertexPositions.length) :
    pointEval (PeriodicGridDrawing.Arithmetic.vertex (front.length+6) index) (front++context input) =
      input.2.vertexPositions[i] := by
  rw [drawing_layout] at he ⊢
  rw [← drawingFront_length]
  exact PeriodicGridDrawing.Arithmetic.vertex_eval_suffix _ _ _ _ _ he hi

theorem routeStart_eval (input : Input Nat) (front : List Nat) :
    (RouteProgram.routeStart front.length).eval (front++context input) =
      front.length+11+6*input.2.indexedSegments.length+2*input.2.vertexPositions.length := by
  have hs := drawing_header_eval input front ⟨2,by decide⟩
  have hv := drawing_header_eval input front ⟨3,by decide⟩
  simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] at hs hv
  simp only [RouteProgram.routeStart,eval_add,eval_literal,eval_mul,
    show front.length+8=front.length+6+2 by omega,
    show front.length+9=front.length+6+3 by omega,hs,hv]
  rfl

end LeanTrominoes.PeriodicPlanarSAT.RouteInput

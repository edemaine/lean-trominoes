/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMGraphIndices
import LeanTrominoes.PeriodicDrawingArithmeticSuffix
import LeanTrominoes.NativeDrawingRouteQueries

/-! # Native instance and drawing queries in the supplied-drawing 3DM encoding -/
namespace LeanTrominoes.PeriodicThreeDM.PlanarQueries
open Gadget NormalizationCompiler BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry

def problemField (depth : Nat) (index : Expr) : Expr := .load (.literal (depth+1)+var depth+index)

theorem problemField_eval (input : Input) (front : List Nat) (index : Expr) :
    (problemField front.length index).eval (front++FlatEncoding.Planar.fields input) =
      (FlatEncoding.fields input.problem)[index.eval (front++FlatEncoding.Planar.fields input)]?.getD 0 := by
  have header : (var front.length).eval (front++FlatEncoding.Planar.fields input) =
      (PeriodicGridDrawing.Arithmetic.fields input.drawing).length := by
    simp [eval_var,List.getElem?_append_right,FlatEncoding.Planar.fields]
  simp only [problemField,Expr.eval,Op.eval,header]
  let leading := front++[(PeriodicGridDrawing.Arithmetic.fields input.drawing).length]++
    PeriodicGridDrawing.Arithmetic.fields input.drawing
  have layout : front++FlatEncoding.Planar.fields input = leading++FlatEncoding.fields input.problem := by
    simp [leading,FlatEncoding.Planar.fields,List.append_assoc]
  have size : leading.length = front.length+1+(PeriodicGridDrawing.Arithmetic.fields input.drawing).length := by simp [leading]; omega
  rw [layout,List.getElem?_append_right (by rw [size]; omega),size]
  congr 2
  omega

def entry (depth : Nat) (index : Expr) (color : WireColor) (field : Fin 3) : Expr :=
  problemField depth (4+9*index+.literal (3*FieldQueries.colorIndex color+field.val))

theorem entry_eval (input : Input) (front : List Nat) (index : Expr) (color : WireColor) (field : Fin 3)
    (i : Nat) (he : index.eval (front++FlatEncoding.Planar.fields input)=i) (hi : i < input.problem.triples.length) :
    (entry front.length index color field).eval (front++FlatEncoding.Planar.fields input) =
      (FlatEncoding.referenceFields (input.problem.triples[i].reference color))[field.val]?.getD 0 := by
  rw [entry,problemField_eval]
  have h := FieldQueries.entry_eval input.problem [] (.literal i) color field hi
  change (FlatEncoding.fields input.problem)[4+9*i+(3*FieldQueries.colorIndex color+field.val)]?.getD 0 = _ at h
  simpa only [eval_add,eval_mul,eval_nat,eval_literal,he,Expr.eval,Op.eval] using h

def vertex (depth : Nat) (index : Expr) : Point := PeriodicGridDrawing.Arithmetic.vertex (depth+1) index

theorem vertex_eval (input : Input) (front : List Nat) (index : Expr) (i : Nat)
    (he : index.eval (front++FlatEncoding.Planar.fields input)=i) (hi : i < input.drawing.vertexPositions.length) :
    pointEval (vertex front.length index) (front++FlatEncoding.Planar.fields input) = input.drawing.vertexPositions[i] := by
  let leading := front++[(PeriodicGridDrawing.Arithmetic.fields input.drawing).length]
  have layout : leading++PeriodicGridDrawing.Arithmetic.fields input.drawing++FlatEncoding.fields input.problem =
      front++FlatEncoding.Planar.fields input := by simp [leading,FlatEncoding.Planar.fields,List.append_assoc]
  have len : leading.length=front.length+1 := by simp [leading]
  have h := PeriodicGridDrawing.Arithmetic.vertex_eval_suffix input.drawing leading
    (FlatEncoding.fields input.problem) index i (by simpa only [layout] using he) hi
  simpa only [vertex,len,layout] using h

theorem drawing_period (input : Input) (front : List Nat) :
    (var (front.length+1)).eval (front++FlatEncoding.Planar.fields input) = input.drawing.gridSize := by
  rw [eval_var,List.getElem?_append_right (by omega)]
  simp [FlatEncoding.Planar.fields,PeriodicGridDrawing.Arithmetic.fields]

theorem header_eval (input : Input) (front : List Nat) (i : Fin 4) :
    (problemField front.length (.literal i.val)).eval (front++FlatEncoding.Planar.fields input) =
      [input.problem.redCount,input.problem.greenCount,input.problem.blueCount,input.problem.triples.length][i.val]?.getD 0 := by
  rw [problemField_eval]
  fin_cases i <;> rfl

def colorPrefixExpr (depth : Nat) : WireColor → Expr
  | .red => 0
  | .green => problemField depth 0
  | .blue => problemField depth 0+problemField depth 1

def targetIndex (depth : Nat) (index : Expr) (color : WireColor) : Expr :=
  problemField depth 3+colorPrefixExpr depth color+entry depth index color 0

theorem targetIndex_eval (input : Input) (front : List Nat) (index : Expr) (color : WireColor)
    (i : Nat) (he : index.eval (front++FlatEncoding.Planar.fields input)=i) (hi : i < input.problem.triples.length) :
    (targetIndex front.length index color).eval (front++FlatEncoding.Planar.fields input) =
      input.problem.elementVertexIndex color (input.problem.triples[i].reference color).atom := by
  have atom := entry_eval input front index color 0 i he hi
  change (entry front.length index color 0).eval (front++FlatEncoding.Planar.fields input) =
    (input.problem.triples[i].reference color).atom at atom
  have hr := header_eval input front 0
  have hg := header_eval input front 1
  have hn := header_eval input front 3
  cases color <;> simp only [targetIndex,colorPrefixExpr,eval_add,atom,elementVertexIndex,colorPrefix]
  all_goals change _ = _
  all_goals simp only [show (problemField front.length 0).eval (front++FlatEncoding.Planar.fields input)=input.problem.redCount from hr,
    show (problemField front.length 1).eval (front++FlatEncoding.Planar.fields input)=input.problem.greenCount from hg,
    show (problemField front.length 3).eval (front++FlatEncoding.Planar.fields input)=input.problem.triples.length from hn]
  all_goals rfl

def offsetPoint (depth : Nat) (index : Expr) (color : WireColor) : Point :=
  (fromCode (entry depth index color 1),fromCode (entry depth index color 2))

theorem offsetPoint_eval (input : Input) (front : List Nat) (index : Expr) (color : WireColor)
    (i : Nat) (he : index.eval (front++FlatEncoding.Planar.fields input)=i) (hi : i < input.problem.triples.length) :
    pointEval (offsetPoint front.length index color) (front++FlatEncoding.Planar.fields input) =
      (input.problem.triples[i].reference color).offset := by
  have hx := entry_eval input front index color 1 i he hi
  have hy := entry_eval input front index color 2 i he hi
  change (entry front.length index color 1).eval (front++FlatEncoding.Planar.fields input) =
    Encodable.encode (input.problem.triples[i].reference color).offset.1 at hx
  change (entry front.length index color 2).eval (front++FlatEncoding.Planar.fields input) =
    Encodable.encode (input.problem.triples[i].reference color).offset.2 at hy
  exact Prod.ext (fromCode_eval _ _ _ hx) (fromCode_eval _ _ _ hy)

end LeanTrominoes.PeriodicThreeDM.PlanarQueries

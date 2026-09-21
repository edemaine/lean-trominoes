/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic
import LeanTrominoes.LocalIncidenceDrawing

/-! # Signed grid geometry in the bounded-arithmetic machine language

Integers are represented by differences of natural-valued expressions.
Comparisons use cross sums, avoiding truncated signed subtraction.
-/
namespace LeanTrominoes.BoundedArithmetic.SignedGeometry
open Expr

structure Signed where
  positive : Expr
  negative : Expr

def Signed.eval (e : Signed) (values : List Nat) : Int :=
  (e.positive.eval values : Int) - e.negative.eval values

def fromCode (code : Expr) : Signed :=
  ⟨.ite (code%2) 0 (code/2),.ite (code%2) (code/2+1) 0⟩

theorem fromCode_eval (code : Expr) (values : List Nat) (n : Int)
    (h : code.eval values = Encodable.encode n) : (fromCode code).eval values = n := by
  cases n with
  | ofNat n =>
    change code.eval values = 2*n at h
    simp [fromCode,Signed.eval,Expr.eval,Op.eval,h]
  | negSucc n =>
    change code.eval values = 2*n+1 at h
    simp [fromCode,Signed.eval,Expr.eval,Op.eval,h]
    omega

def add (a b : Signed) : Signed := ⟨a.positive+b.positive,a.negative+b.negative⟩
def scale (n : Expr) (a : Signed) : Signed := ⟨n*a.positive,n*a.negative⟩
def difference (a b : Expr) : Signed := ⟨a,b⟩

def equal (a b : Signed) : Expr := eqE (a.positive+b.negative) (b.positive+a.negative)
def less (a b : Signed) : Expr := ltE (a.positive+b.negative) (b.positive+a.negative)
def lessEqual (a b : Signed) : Expr := leE (a.positive+b.negative) (b.positive+a.negative)

@[simp] theorem add_eval (a b : Signed) (v : List Nat) : (add a b).eval v = a.eval v+b.eval v := by
  simp [add,Signed.eval,Expr.eval,Op.eval]; omega
@[simp] theorem scale_eval (n : Expr) (a : Signed) (v : List Nat) :
    (scale n a).eval v = (n.eval v:Int)*a.eval v := by
  simp [scale,Signed.eval,Expr.eval,Op.eval,mul_sub]
@[simp] theorem difference_eval (a b : Expr) (v : List Nat) :
    (difference a b).eval v = (a.eval v:Int)-b.eval v := rfl
@[simp] theorem equal_truth (a b : Signed) (v : List Nat) :
    (equal a b).Truth v ↔ a.eval v=b.eval v := by
  simp only [equal,truth_eq,eval_add,Signed.eval]; omega
@[simp] theorem less_truth (a b : Signed) (v : List Nat) :
    (less a b).Truth v ↔ a.eval v<b.eval v := by
  simp only [less,truth_lt,eval_add,Signed.eval]; omega
@[simp] theorem lessEqual_truth (a b : Signed) (v : List Nat) :
    (lessEqual a b).Truth v ↔ a.eval v≤b.eval v := by
  simp only [lessEqual,truth_le,eval_add,Signed.eval]; omega

abbrev Point := Signed × Signed

def pointEval (p : Point) (v : List Nat) : Cell := (p.1.eval v,p.2.eval v)
def pointAdd (a b : Point) : Point := (add a.1 b.1,add a.2 b.2)
def pointScale (n : Expr) (a : Point) : Point := (scale n a.1,scale n a.2)

structure Segment where
  start : Point
  finish : Point

def Segment.eval (s : Segment) (v : List Nat) : GridSegment := ⟨pointEval s.start v,pointEval s.finish v⟩
def translate (s : Segment) (p : Point) : Segment := ⟨pointAdd p s.start,pointAdd p s.finish⟩

@[simp] theorem pointAdd_eval (a b : Point) (v : List Nat) :
    pointEval (pointAdd a b) v = Cell.add (pointEval a v) (pointEval b v) := by
  simp [pointEval,pointAdd,Cell.add]
@[simp] theorem pointScale_eval (n : Expr) (a : Point) (v : List Nat) :
    pointEval (pointScale n a) v = Cell.scale (n.eval v) (pointEval a v) := by
  simp [pointEval,pointScale,Cell.scale]
@[simp] theorem translate_eval (s : Segment) (p : Point) (v : List Nat) :
    (translate s p).eval v = (s.eval v).translate (pointEval p v) := by
  simp [translate,Segment.eval,GridSegment.translate]

def between (a b p : Signed) : Expr :=
  orE (andE (lessEqual a p) (lessEqual p b)) (andE (lessEqual b p) (lessEqual p a))
def strictlyBetween (a b p : Signed) : Expr :=
  orE (andE (less a p) (less p b)) (andE (less b p) (less p a))
def minLessMax (a b c d : Signed) : Expr :=
  orE (orE (less a c) (less a d)) (orE (less b c) (less b d))
def overlap (a b c d : Signed) : Expr := andE (minLessMax a b c d) (minLessMax c d a b)
def horizontal (s : Segment) : Expr := andE (equal s.start.2 s.finish.2) (notE (equal s.start.1 s.finish.1))
def vertical (s : Segment) : Expr := andE (equal s.start.1 s.finish.1) (notE (equal s.start.2 s.finish.2))
def contains (s : Segment) (p : Point) : Expr :=
  orE (andE (horizontal s) (andE (equal p.2 s.start.2) (between s.start.1 s.finish.1 p.1)))
    (andE (vertical s) (andE (equal p.1 s.start.1) (between s.start.2 s.finish.2 p.2)))
def interiorContains (s : Segment) (p : Point) : Expr :=
  orE (andE (horizontal s) (andE (equal p.2 s.start.2) (strictlyBetween s.start.1 s.finish.1 p.1)))
    (andE (vertical s) (andE (equal p.1 s.start.1) (strictlyBetween s.start.2 s.finish.2 p.2)))
def interiorsMeet (a b : Segment) : Expr :=
  orE (andE (horizontal a) (andE (horizontal b) (andE (equal a.start.2 b.start.2)
    (overlap a.start.1 a.finish.1 b.start.1 b.finish.1))))
  (orE (andE (vertical a) (andE (vertical b) (andE (equal a.start.1 b.start.1)
    (overlap a.start.2 a.finish.2 b.start.2 b.finish.2))))
  (orE (andE (horizontal a) (andE (vertical b) (andE
    (strictlyBetween a.start.1 a.finish.1 b.start.1) (strictlyBetween b.start.2 b.finish.2 a.start.2))))
    (andE (vertical a) (andE (horizontal b) (andE
    (strictlyBetween b.start.1 b.finish.1 a.start.1) (strictlyBetween a.start.2 a.finish.2 b.start.2))))))

@[simp] theorem between_truth (a b p : Signed) (v : List Nat) :
    (between a b p).Truth v ↔ GridSegment.Between (a.eval v) (b.eval v) (p.eval v) := by
  simp [between,GridSegment.Between]
@[simp] theorem strictlyBetween_truth (a b p : Signed) (v : List Nat) :
    (strictlyBetween a b p).Truth v ↔ GridSegment.StrictlyBetween (a.eval v) (b.eval v) (p.eval v) := by
  simp [strictlyBetween,GridSegment.StrictlyBetween]
@[simp] theorem overlap_truth (a b c d : Signed) (v : List Nat) :
    (overlap a b c d).Truth v ↔ GridSegment.OpenIntervalsOverlap (a.eval v) (b.eval v) (c.eval v) (d.eval v) := by
  simp [overlap,minLessMax,GridSegment.OpenIntervalsOverlap]
  tauto
@[simp] theorem horizontal_truth (s : Segment) (v : List Nat) :
    (horizontal s).Truth v ↔ (s.eval v).IsHorizontal := by
  simp [horizontal,GridSegment.IsHorizontal,Segment.eval,pointEval]
@[simp] theorem vertical_truth (s : Segment) (v : List Nat) :
    (vertical s).Truth v ↔ (s.eval v).IsVertical := by
  simp [vertical,GridSegment.IsVertical,Segment.eval,pointEval]
@[simp] theorem contains_truth (s : Segment) (p : Point) (v : List Nat) :
    (contains s p).Truth v ↔ (s.eval v).Contains (pointEval p v) := by
  simp [contains,GridSegment.Contains,Segment.eval,pointEval]
@[simp] theorem interiorContains_truth (s : Segment) (p : Point) (v : List Nat) :
    (interiorContains s p).Truth v ↔ (s.eval v).InteriorContains (pointEval p v) := by
  simp [interiorContains,GridSegment.InteriorContains,Segment.eval,pointEval]
@[simp] theorem interiorsMeet_truth (a b : Segment) (v : List Nat) :
    (interiorsMeet a b).Truth v ↔ GridSegment.InteriorsMeet (a.eval v) (b.eval v) := by
  simp [interiorsMeet,GridSegment.InteriorsMeet,Segment.eval,pointEval]

end LeanTrominoes.BoundedArithmetic.SignedGeometry

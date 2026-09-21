/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticSignedResidue
import LeanTrominoes.PeriodicDrawingArithmeticGeometry
import LeanTrominoes.PeriodicGraphOrbitCertificate

/-! # Compiled vertex distinctness and fundamental-square guards -/
namespace LeanTrominoes.PeriodicGridDrawing.VertexPredicate
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry Arithmetic

def comparison (orbit : Bool) : Expr :=
  if orbit then pointEqualModulo (var 2) (vertex 2 (var 1)) (vertex 2 (var 0))
    else pointEqual (vertex 2 (var 1)) (vertex 2 (var 0))
def unique (orbit : Bool) : Expr :=
  .all (var 3) (.all (var 4) (impE (comparison orbit) (eqE (var 1) (var 0))))
def inSquare (period : Expr) (p : Point) : Expr :=
  andE (less (difference 0 0) p.1) (andE (less p.1 (difference period 0))
    (andE (less (difference 0 0) p.2) (less p.2 (difference period 0))))
def square : Expr := .all (var 3) (inSquare (var 1) (vertex 1 (var 0)))
def predicate (orbit : Bool) : Expr := if orbit then unique true else andE (unique false) square
def decision (orbit : Bool) : Expr := .ite (predicate orbit) 1 0

def position (orbit : Bool) (d : PeriodicGridDrawing) (p : Cell) : Cell :=
  if orbit then OrbitCertificate.residue d.gridSize p else p

theorem comparison_truth (orbit : Bool) (d : PeriodicGridDrawing)
    (i j : Nat) (hi : i<d.vertexPositions.length) (hj : j<d.vertexPositions.length) :
    (comparison orbit).Truth (j::i::fields d) ↔
      position orbit d d.vertexPositions[i] = position orbit d d.vertexPositions[j] := by
  have a := vertex_eval d [j,i] (var 1) i rfl hi
  have b := vertex_eval d [j,i] (var 0) j rfl hj
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,List.cons_append,List.nil_append] at a b
  have period : (var 2).eval (j::i::fields d) = d.gridSize := rfl
  cases orbit with
  | false =>
    change (pointEqual (vertex 2 (var 1)) (vertex 2 (var 0))).Truth _ ↔ _
    rw [pointEqual_truth,a,b]
    rfl
  | true =>
    change (pointEqualModulo (var 2) (vertex 2 (var 1)) (vertex 2 (var 0))).Truth _ ↔ _
    rw [pointEqualModulo_truth,a,b,period]
    rfl

private theorem nodup_map_iff {α β : Type} (xs : List α) (f : α → β) :
    (xs.map f).Nodup ↔ ∀ i (hi : i<xs.length), ∀ j (hj : j<xs.length), f xs[i] = f xs[j] → i=j := by
  rw [List.nodup_iff_injective_getElem]
  constructor
  · intro h i hi j hj eq
    have equal := @h ⟨i,by simpa using hi⟩ ⟨j,by simpa using hj⟩ (by simpa using eq)
    exact congrArg Fin.val equal
  · intro h i j eq
    apply Fin.ext
    exact h i.val (by simpa using i.isLt) j.val (by simpa using j.isLt) (by simpa using eq)

theorem unique_truth (orbit : Bool) (d : PeriodicGridDrawing) :
    (unique orbit).Truth (fields d) ↔ (d.vertexPositions.map (position orbit d)).Nodup := by
  simp only [unique,truth_all]
  change (∀ i<d.vertexPositions.length, ∀ j<d.vertexPositions.length,
    (impE (comparison orbit) (eqE (var 1) (var 0))).Truth (j::i::fields d)) ↔ _
  rw [nodup_map_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  simp only [truth_imp,comparison_truth orbit d i j hi hj,truth_eq,eval_var,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]

theorem inSquare_truth (period : Expr) (p : Point) (v : List Nat) :
    (inSquare period p).Truth v ↔
      0 < (pointEval p v).1 ∧ (pointEval p v).1 < (period.eval v:Int) ∧
      0 < (pointEval p v).2 ∧ (pointEval p v).2 < (period.eval v:Int) := by
  simp [inSquare,truth_and,less_truth,difference_eval,pointEval,Expr.eval]

theorem square_truth (d : PeriodicGridDrawing) :
    square.Truth (fields d) ↔ ∀ p ∈ d.vertexPositions, d.PositionInFundamentalSquare p := by
  simp only [square,truth_all]
  change (∀ i<d.vertexPositions.length, (inSquare (var 1) (vertex 1 (var 0))).Truth (i::fields d)) ↔ _
  have body (i : Nat) (hi : i<d.vertexPositions.length) :
      (inSquare (var 1) (vertex 1 (var 0))).Truth (i::fields d) ↔
        d.PositionInFundamentalSquare d.vertexPositions[i] := by
    have h := vertex_eval d [i] (var 0) i rfl hi
    simp only [List.length_cons,List.length_nil,Nat.reduceAdd,List.cons_append,List.nil_append] at h
    rw [inSquare_truth,h]
    rfl
  calc
    _ ↔ ∀ i (hi : i<d.vertexPositions.length), d.PositionInFundamentalSquare d.vertexPositions[i] := by
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      exact body i hi
    _ ↔ _ := by
      constructor
      · intro h p hp
        obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
        exact h i hi
      · intro h i hi
        exact h _ (List.getElem_mem hi)

def Valid (orbit : Bool) (d : PeriodicGridDrawing) : Prop :=
  if orbit then (d.vertexPositions.map (OrbitCertificate.residue d.gridSize)).Nodup
    else d.vertexPositions.Nodup ∧ ∀ p ∈ d.vertexPositions, d.PositionInFundamentalSquare p

theorem predicate_truth (orbit : Bool) (d : PeriodicGridDrawing) :
    (predicate orbit).Truth (fields d) ↔ Valid orbit d := by
  cases orbit with
  | false =>
    simp only [predicate,Bool.false_eq_true,if_false,truth_and,unique_truth,square_truth,Valid]
    change ((d.vertexPositions.map id).Nodup ∧ _) ↔ _
    rw [List.map_id]
  | true =>
    simp only [predicate,if_true,unique_truth,Valid]
    rfl

theorem decision_noPower (orbit : Bool) : (decision orbit).noPower = true := by cases orbit <;> decide

end LeanTrominoes.PeriodicGridDrawing.VertexPredicate

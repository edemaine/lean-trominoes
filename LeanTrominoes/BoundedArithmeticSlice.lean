/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PartrecBoundedArithmeticAutomaticSpace

/-! # Bounded arithmetic on a length-delimited component

`slice` reads the component following its length header and ignores every
subsequent component. Local bindings remain accessible. Out-of-range loads
return zero, exactly as on the isolated component.
-/
namespace LeanTrominoes.BoundedArithmetic

private def sliceLoad (depth : Nat) (index : Expr) : Expr :=
  .ite (.binary .lt index (.literal depth)) (.load index)
    (.ite (.binary .lt index
      (.binary .add (.literal depth) (.load (.literal depth))))
      (.load (.binary .add index (.literal 1))) (.literal 0))

def Expr.slice : Expr → Nat → Expr
  | .literal n, _ => .literal n
  | .load i, depth => sliceLoad depth (i.slice depth)
  | .binary op a b, depth => .binary op (a.slice depth) (b.slice depth)
  | .testBit a b, depth => .testBit (a.slice depth) (b.slice depth)
  | .powerTwo a, depth => .powerTwo (a.slice depth)
  | .ite t y n, depth => .ite (t.slice depth) (y.slice depth) (n.slice depth)
  | .letE a b, depth => .letE (a.slice depth) (b.slice (depth+1))
  | .all n b, depth => .all (n.slice depth) (b.slice (depth+1))

private theorem sliceLoad_eval (leading component rest : List Nat) (index : Expr) :
    (sliceLoad leading.length index).eval (leading ++ component.length :: (component ++ rest)) =
      (leading ++ component)[index.eval (leading ++ component.length :: (component ++ rest))]?.getD 0 := by
  have header : (leading ++ component.length :: (component ++ rest))[leading.length]? = some component.length := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  simp only [sliceLoad,Expr.eval,Op.eval,header,Option.getD_some]
  generalize index.eval (leading ++ component.length :: (component ++ rest)) = i
  by_cases h : i < leading.length
  · simp [h,List.getElem?_append_left h]
  · have hi : leading.length ≤ i := by omega
    have hi' : leading.length ≤ i+1 := by omega
    simp only [h,if_false,ite_true,List.getElem?_append_right hi,
      List.getElem?_append_right hi']
    by_cases bound : i < leading.length + component.length
    · have small : i - leading.length < component.length := by omega
      have eqn : i+1-leading.length = (i-leading.length)+1 := by omega
      simp [bound,eqn,List.getElem?_cons_succ,List.getElem?_append_left small]
    · have large : component.length ≤ i-leading.length := by omega
      simp [bound,List.getElem?_eq_none_iff.mpr large]

theorem Expr.slice_eval (expr : Expr) (leading component rest : List Nat) :
    (expr.slice leading.length).eval (leading ++ component.length :: (component ++ rest)) =
      expr.eval (leading ++ component) := by
  induction expr generalizing leading with
  | literal n => rfl
  | load i ih => simp only [Expr.slice,sliceLoad_eval,ih,Expr.eval]
  | binary op a b ia ib => simp only [Expr.slice,Expr.eval,ia,ib]
  | testBit a b ia ib => simp only [Expr.slice,Expr.eval,ia,ib]
  | powerTwo a ih => simp only [Expr.slice,Expr.eval,ih]
  | ite t y n it iy ino => simp only [Expr.slice,Expr.eval,it,iy,ino]
  | letE a b ia ib =>
    simp only [Expr.slice,Expr.eval,ia]
    exact ib (a.eval (leading ++ component) :: leading)
  | all n b ino ib =>
    simp only [Expr.slice,Expr.eval,ino]
    congr 2
    funext i
    rw [show (b.slice (leading.length+1)).eval
      (i :: (leading ++ component.length :: (component ++ rest))) =
      b.eval (i :: (leading ++ component)) from ib (i::leading)]

theorem Expr.slice_noPower (expr : Expr) (depth : Nat) :
    (expr.slice depth).noPower = expr.noPower := by
  induction expr generalizing depth <;>
    simp_all [Expr.slice,sliceLoad,Expr.noPower,Bool.and_self]

end LeanTrominoes.BoundedArithmetic

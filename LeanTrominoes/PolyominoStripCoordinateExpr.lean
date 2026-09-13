/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic
import LeanTrominoes.PolyominoStripArithmeticGeometry

/-! # Compiled arithmetic expressions for signed coordinates and orientations -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr

/-- Natural expressions for the signed-coordinate encoding. -/
def negate (code : Expr) : Expr :=
  .ite (eqE (code%2) 0) (.ite (eqE code 0) 0 (code-1)) (code+1)

def biased (bound code : Expr) : Expr :=
  .ite (eqE (code%2) 0) (bound+code/2) (bound-(code/2+1))

def orientX (symmetry x y : Expr) : Expr :=
  let base := .ite (eqE (symmetry%2) 0) x y
  .ite (orE (eqE symmetry 1) (orE (eqE symmetry 2) (orE (eqE symmetry 6) (eqE symmetry 7))))
    (negate base) base

def orientY (symmetry x y : Expr) : Expr :=
  let base := .ite (eqE (symmetry%2) 0) y x
  .ite (orE (eqE symmetry 2) (orE (eqE symmetry 3) (orE (eqE symmetry 4) (eqE symmetry 7))))
    (negate base) base

@[simp] theorem negate_eval (code : Expr) (values : List Nat) :
    (negate code).eval values = Arithmetic.negateCode (code.eval values) := by
  by_cases h : code.eval values % 2 = 0 <;> by_cases hz : code.eval values = 0 <;>
    simp [negate,eqE,Expr.eval,Op.eval,Arithmetic.negateCode,h,hz]

@[simp] theorem biased_eval (bound code : Expr) (values : List Nat) :
    (biased bound code).eval values = Arithmetic.bias (bound.eval values) (code.eval values) := by
  by_cases h : code.eval values % 2 = 0 <;>
    simp [biased,eqE,Expr.eval,Op.eval,Arithmetic.bias,h]

@[simp] theorem orientX_eval (symmetry x y : Expr) (values : List Nat) :
    (orientX symmetry x y).eval values = Arithmetic.orientedX (symmetry.eval values) (x.eval values) (y.eval values) := by
  by_cases h1 : symmetry.eval values = 1 <;> by_cases h2 : symmetry.eval values = 2 <;>
    by_cases h6 : symmetry.eval values = 6 <;> by_cases h7 : symmetry.eval values = 7 <;>
    by_cases he : symmetry.eval values % 2 = 0 <;>
    simp [orientX,orE,eqE,Expr.eval,Op.eval,negate_eval,Arithmetic.orientedX,h1,h2,h6,h7,he]

@[simp] theorem orientY_eval (symmetry x y : Expr) (values : List Nat) :
    (orientY symmetry x y).eval values = Arithmetic.orientedY (symmetry.eval values) (x.eval values) (y.eval values) := by
  by_cases h2 : symmetry.eval values = 2 <;> by_cases h3 : symmetry.eval values = 3 <;>
    by_cases h4 : symmetry.eval values = 4 <;> by_cases h7 : symmetry.eval values = 7 <;>
    by_cases he : symmetry.eval values % 2 = 0 <;>
    simp [orientY,orE,eqE,Expr.eval,Op.eval,negate_eval,Arithmetic.orientedY,h2,h3,h4,h7,he]

def inside (height bound symmetry y xcode ycode : Expr) : Expr :=
  let translated := y+biased bound (orientY symmetry xcode ycode)
  andE (leE (2*bound) translated) (ltE translated (height+2*bound))

def covers (bound symmetry column y row xcode ycode : Expr) : Expr :=
  andE (eqE (column+biased bound (orientX symmetry xcode ycode)) (2*bound))
    (eqE (y+biased bound (orientY symmetry xcode ycode)) (row+2*bound))

@[simp] theorem inside_truth (height bound symmetry y xcode ycode : Expr) (values : List Nat) :
    (inside height bound symmetry y xcode ycode).Truth values ↔
      (2*bound.eval values ≤ y.eval values+Arithmetic.bias (bound.eval values)
          (Arithmetic.orientedY (symmetry.eval values) (xcode.eval values) (ycode.eval values)) ∧
        y.eval values+Arithmetic.bias (bound.eval values)
          (Arithmetic.orientedY (symmetry.eval values) (xcode.eval values) (ycode.eval values)) <
            height.eval values+2*bound.eval values) := by
  simp [inside]
  rfl

@[simp] theorem covers_truth (bound symmetry column y row xcode ycode : Expr) (values : List Nat) :
    (covers bound symmetry column y row xcode ycode).Truth values ↔
      (column.eval values+Arithmetic.bias (bound.eval values)
          (Arithmetic.orientedX (symmetry.eval values) (xcode.eval values) (ycode.eval values)) = 2*bound.eval values ∧
        y.eval values+Arithmetic.bias (bound.eval values)
          (Arithmetic.orientedY (symmetry.eval values) (xcode.eval values) (ycode.eval values)) =
            row.eval values+2*bound.eval values) := by
  simp [covers]
  rfl

theorem negate_noPower (code : Expr) (h : code.noPower = true) : (negate code).noPower = true := by
  simp [negate,eqE,Expr.noPower,h]

theorem biased_noPower (bound code : Expr) (hb : bound.noPower = true) (hc : code.noPower = true) :
    (biased bound code).noPower = true := by simp [biased,eqE,Expr.noPower,hb,hc]

theorem orientX_noPower (symmetry x y : Expr)
    (hs : symmetry.noPower = true) (hx : x.noPower = true) (hy : y.noPower = true) :
    (orientX symmetry x y).noPower = true := by
  simp [orientX,negate,orE,eqE,Expr.noPower,hs,hx,hy]

theorem orientY_noPower (symmetry x y : Expr)
    (hs : symmetry.noPower = true) (hx : x.noPower = true) (hy : y.noPower = true) :
    (orientY symmetry x y).noPower = true := by
  simp [orientY,negate,orE,eqE,Expr.noPower,hs,hx,hy]

end LeanTrominoes.PolyominoStripWindow.Formula

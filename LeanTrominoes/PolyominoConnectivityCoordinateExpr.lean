/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCoordinateExpr
import LeanTrominoes.PolyominoConnectivity

/-! # Exact signed adjacency tests using natural coordinate codes -/

namespace LeanTrominoes.PolyominoConnectivitySearch.Formula
open BoundedArithmetic BoundedArithmetic.Expr

def successor (code : Expr) : Expr :=
  .ite (eqE (code%2) 0) (code+2) (.ite (eqE code 1) 0 (code-2))

theorem successor_eval (code : Expr) (values : List Nat) (z : Int)
    (h : code.eval values = Encodable.encode z) :
    (successor code).eval values = Encodable.encode (z+1) := by
  simp only [successor,Expr.eval,eqE,eval_mod,eval_nat,eval_add,eval_sub,Op.eval,h]
  cases z with
  | ofNat n =>
    change (if (if (2*n)%2 = 0 then 1 else 0) = 0 then _ else 2*n+2) = 2*(n+1)
    have parity : (2*n)%2 = 0 := by omega
    simp only [if_pos parity,show (1 : Nat) ≠ 0 from by decide,if_false]
    omega
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      change (if (if (2*(n+1)+1)%2 = 0 then 1 else 0) = 0 then
        (if (if 2*(n+1)+1 = 1 then 1 else 0) = 0 then 2*(n+1)+1-2 else 0)
        else _) = 2*n+1
      have parity : (2*(n+1)+1)%2 ≠ 0 := by omega
      simp only [if_neg parity,if_pos rfl,show 2*(n+1)+1 ≠ 1 from by omega,if_false,if_true]
      omega

def neighbours (x y u v : Expr) : Expr :=
  orE (andE (eqE x u) (eqE y v))
    (orE (andE (eqE x u) (orE (eqE (successor y) v) (eqE (successor v) y)))
      (andE (eqE y v) (orE (eqE (successor x) u) (eqE (successor u) x))))

theorem neighbours_truth (x y u v : Expr) (values : List Nat) (a b : Cell)
    (hx : x.eval values = Encodable.encode a.1) (hy : y.eval values = Encodable.encode a.2)
    (hu : u.eval values = Encodable.encode b.1) (hv : v.eval values = Encodable.encode b.2) :
    (neighbours x y u v).Truth values ↔ a = b ∨ Cell.SideAdjacent a b := by
  simp only [neighbours,truth_or,truth_and,truth_eq,
    successor_eval _ _ _ hx,successor_eval _ _ _ hy,
    successor_eval _ _ _ hu,successor_eval _ _ _ hv,hx,hy,hu,hv,
    Encodable.encode_injective.eq_iff,Prod.ext_iff,Cell.SideAdjacent]

theorem neighbours_noPower (x y u v : Expr)
    (hx : x.noPower = true) (hy : y.noPower = true) (hu : u.noPower = true) (hv : v.noPower = true) :
    (neighbours x y u v).noPower = true := by
  simp [neighbours,successor,andE,orE,eqE,Expr.noPower,hx,hy,hu,hv]

end LeanTrominoes.PolyominoConnectivitySearch.Formula

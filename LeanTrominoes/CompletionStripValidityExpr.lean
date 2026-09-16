/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripFieldExpr
import LeanTrominoes.CompletionStripRawValidity

/-! # Compiled bounded-arithmetic prefill validity -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw
open BoundedArithmetic BoundedArithmetic.Expr

def allThree (f : Fin 3 → Expr) : Expr := andE (f 0) (andE (f 1) (f 2))
def anyThree (f : Fin 3 → Expr) : Expr := orE (f 0) (orE (f 1) (f 2))

@[simp] theorem allThree_truth (f : Fin 3 → Expr) (values : List Nat) :
    (allThree f).Truth values ↔ ∀ k, (f k).Truth values := by
  simp [allThree,Fin.forall_fin_succ]

@[simp] theorem anyThree_truth (f : Fin 3 → Expr) (values : List Nat) :
    (anyThree f).Truth values ↔ ∃ k, (f k).Truth values := by
  simp [anyThree,Fin.exists_fin_succ]

def insideExpr (t : Tromino) (depth : Nat) (p : Expr) : Expr := allThree fun k =>
  andE (leE (var depth) (cellY t depth p (.literal k.val)))
    (ltE (cellY t depth p (.literal k.val)) (var depth + var (depth+1)))

def sameExpr (t : Tromino) (depth : Nat) (p q : Expr) (a b : Fin 3) : Expr :=
  andE (eqE (cellY t depth p (.literal a.val)) (cellY t depth q (.literal b.val)))
    (eqE (cellX t depth p (.literal a.val) % var (depth+2))
      (cellX t depth q (.literal b.val) % var (depth+2)))

def alignedExpr (t : Tromino) (depth : Nat) (p q : Expr) (a b c d : Fin 3) : Expr :=
  andE (eqE (cellX t depth p (.literal c.val) + cellX t depth q (.literal b.val))
    (cellX t depth q (.literal d.val) + cellX t depth p (.literal a.val)))
  (eqE (cellY t depth p (.literal c.val) + cellY t depth q (.literal b.val))
    (cellY t depth q (.literal d.val) + cellY t depth p (.literal a.val)))

def pairExpr (t : Tromino) (depth : Nat) (p q : Expr) : Expr :=
  allThree fun a => allThree fun b => impE (sameExpr t depth p q a b)
    (andE (allThree fun c => anyThree fun d => alignedExpr t depth p q a b c d)
      (allThree fun d => anyThree fun c => alignedExpr t depth p q a b c d))

def validExpr (t : Tromino) : Expr :=
  andE (.all (var 3) (insideExpr t 1 (var 0)))
    (.all (var 3) (.all (var 4) (pairExpr t 2 (var 1) (var 0))))

theorem insideExpr_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (p : Expr) (i : Nat) (hi : i < input.motif.length) (hp : p.eval (front++fields input) = i) :
    (insideExpr t front.length p).Truth (front++fields input) ↔
      ∀ k : Fin 3, bound input ≤ (biasedCell t (bound input) input.motif[i] k).2 ∧
        (biasedCell t (bound input) input.motif[i] k).2 < bound input+input.height := by
  have hb := header_get input front 0 (by decide)
  have hh := header_get input front 1 (by decide)
  simp only [Nat.add_zero] at hb
  simp only [insideExpr,allThree_truth,truth_and,truth_le,truth_lt,eval_add,eval_var,hb,hh]
  apply forall_congr'
  intro k
  rw [(cellXY_eval t input front p (.literal k.val) i k hi hp rfl).2]
  rfl

theorem sameExpr_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (p q : Expr) (i j : Nat) (hi : i < input.motif.length) (hj : j < input.motif.length)
    (hp : p.eval (front++fields input) = i) (hq : q.eval (front++fields input) = j) (a b : Fin 3) :
    (sameExpr t front.length p q a b).Truth (front++fields input) ↔
      SamePlace t input input.motif[i] input.motif[j] a b := by
  have ha := cellXY_eval t input front p (.literal a.val) i a hi hp rfl
  have hb := cellXY_eval t input front q (.literal b.val) j b hj hq rfl
  have period := header_get input front 2 (by decide)
  simp only [sameExpr,truth_and,truth_eq,eval_mod,eval_var,period,ha.1,ha.2,hb.1,hb.2]
  rfl

theorem alignedExpr_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (p q : Expr) (i j : Nat) (hi : i < input.motif.length) (hj : j < input.motif.length)
    (hp : p.eval (front++fields input) = i) (hq : q.eval (front++fields input) = j) (a b c d : Fin 3) :
    (alignedExpr t front.length p q a b c d).Truth (front++fields input) ↔
      Aligned t input input.motif[i] input.motif[j] a b c d := by
  have ha := cellXY_eval t input front p (.literal a.val) i a hi hp rfl
  have hb := cellXY_eval t input front q (.literal b.val) j b hj hq rfl
  have hc := cellXY_eval t input front p (.literal c.val) i c hi hp rfl
  have hd := cellXY_eval t input front q (.literal d.val) j d hj hq rfl
  simp only [alignedExpr,truth_and,truth_eq,eval_add,ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hd.1,hd.2]
  rfl

theorem pairExpr_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (p q : Expr) (i j : Nat) (hi : i < input.motif.length) (hj : j < input.motif.length)
    (hp : p.eval (front++fields input) = i) (hq : q.eval (front++fields input) = j) :
    (pairExpr t front.length p q).Truth (front++fields input) ↔
      ∀ a b, SamePlace t input input.motif[i] input.motif[j] a b →
        (∀ c, ∃ d, Aligned t input input.motif[i] input.motif[j] a b c d) ∧
        (∀ d, ∃ c, Aligned t input input.motif[i] input.motif[j] a b c d) := by
  simp only [pairExpr,allThree_truth,anyThree_truth,truth_imp,truth_and,
    sameExpr_truth t input front p q i j hi hj hp hq,
    alignedExpr_truth t input front p q i j hi hj hp hq]

theorem validExpr_truth (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    (validExpr t).Truth (fields input) ↔ Valid t input := by
  simp only [validExpr,truth_and,truth_all]
  change ((∀ i < input.motif.length, (insideExpr t 1 (var 0)).Truth (i::fields input)) ∧
    ∀ i < input.motif.length, ∀ j < input.motif.length,
      (pairExpr t 2 (var 1) (var 0)).Truth (j::i::fields input)) ↔ _
  have inside (i : Nat) (hi : i < input.motif.length) :=
    insideExpr_truth t input [i] (var 0) i hi rfl
  have pairs (i j : Nat) (hi : i < input.motif.length) (hj : j < input.motif.length) :=
    pairExpr_truth t input [j,i] (var 1) (var 0) i j hi hj rfl rfl
  simp only [List.length_cons,List.length_nil,zero_add,Nat.reduceAdd,List.cons_append,List.nil_append] at inside pairs
  unfold Valid
  constructor
  · rintro ⟨hinside,hpairs⟩
    constructor
    · intro p hp
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
      exact (inside i hi).mp (hinside i hi)
    · intro p hp q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hp
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hq
      exact (pairs i j hi hj).mp (hpairs i hi j hj)
  · rintro ⟨hinside,hpairs⟩
    exact ⟨fun i hi => (inside i hi).mpr (hinside _ (List.getElem_mem hi)),
      fun i hi j hj => (pairs i j hi hj).mpr (hpairs _ (List.getElem_mem hi) _ (List.getElem_mem hj))⟩

theorem validExpr_noPower (t : Tromino) : (validExpr t).noPower = true := by
  cases t <;> simp [validExpr,insideExpr,pairExpr,sameExpr,alignedExpr,allThree,anyThree,
    cellX,cellY,fieldExpr,sourceX,sourceY,PolyominoStripWindow.Formula.biased,
    PolyominoStripWindow.Formula.orientX,PolyominoStripWindow.Formula.orientY,
    PolyominoStripWindow.Formula.negate,andE,orE,impE,leE,notE,eqE,ltE,Expr.noPower]

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw

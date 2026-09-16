/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripRawGeometry
import LeanTrominoes.PolyominoStripCoordinateExpr

/-! # Compiled field access and tromino coordinates -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw
open BoundedArithmetic BoundedArithmetic.Expr PolyominoStripWindow.Formula

private theorem placement_get (ps : List (Placement Unit)) (suffix : List Nat)
    (i : Nat) (axis : Fin 3) (hi : i < ps.length) :
    ((ps.flatMap CompletionStripEncoding.placementFields ++ suffix)[3*i+axis.val]?.getD 0) =
      (CompletionStripEncoding.placementFields ps[i])[axis.val]?.getD 0 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => fin_cases axis <;> simp [CompletionStripEncoding.placementFields]
    | succ i =>
      have h := ih i (by simpa using hi)
      have address : 3*(i+1)+axis.val = (3*i+axis.val)+1+1+1 := by omega
      simpa [CompletionStripEncoding.placementFields,address] using h

theorem header_get (input : PeriodicStripTrominoPrefill) (front : List Nat) (i : Nat) (hi : i < 4) :
    ((front ++ fields input)[front.length+i]?.getD 0) =
      ([bound input,input.height,input.period,input.motif.length][i]?.getD 0) := by
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,fields,CompletionStripEncoding.fields]
  change (([bound input,input.height,input.period,input.motif.length] ++
    input.motif.flatMap CompletionStripEncoding.placementFields)[i]?.getD 0) = _
  rw [List.getElem?_append_left (by simpa using hi)]

theorem placement_field (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (i : Nat) (axis : Fin 3) (hi : i < input.motif.length) :
    ((front ++ fields input)[front.length+4+3*i+axis.val]?.getD 0) =
      (CompletionStripEncoding.placementFields input.motif[i])[axis.val]?.getD 0 := by
  let header := front ++ [bound input,input.height,input.period,input.motif.length]
  have address : front.length+4+3*i+axis.val = header.length+(3*i+axis.val) := by simp [header]; omega
  have structureEq : front ++ fields input = header ++ input.motif.flatMap CompletionStripEncoding.placementFields := by
    simp [header,fields,CompletionStripEncoding.fields,List.append_assoc]
  rw [address,structureEq]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  simpa using placement_get input.motif [] i axis hi

def fieldExpr (depth : Nat) (index : Expr) (axis : Nat) : Expr :=
  .load (.literal (depth+4) + 3*index + .literal axis)

def sourceX (t : Tromino) (k : Expr) : Expr :=
  match t with
  | .I => 2*k
  | .L => .ite (eqE k 1) 2 0

def sourceY (t : Tromino) (k : Expr) : Expr :=
  match t with
  | .I => 0
  | .L => .ite (eqE k 2) 2 0

def cellX (t : Tromino) (depth : Nat) (i k : Expr) : Expr :=
  biased (var depth) (fieldExpr depth i 1) +
    biased 2 (orientX (fieldExpr depth i 0) (sourceX t k) (sourceY t k)) - 2

def cellY (t : Tromino) (depth : Nat) (i k : Expr) : Expr :=
  biased (var depth) (fieldExpr depth i 2) +
    biased 2 (orientY (fieldExpr depth i 0) (sourceX t k) (sourceY t k)) - 2

theorem fieldExpr_eval (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (index : Expr) (i : Nat) (axis : Fin 3)
    (eq : index.eval (front ++ fields input) = i) (hi : i < input.motif.length) :
    (fieldExpr front.length index axis.val).eval (front ++ fields input) =
      (CompletionStripEncoding.placementFields input.motif[i])[axis.val]?.getD 0 := by
  simp only [fieldExpr,Expr.eval,Op.eval,eq]
  exact placement_field input front i axis hi

theorem sourceX_eval (t : Tromino) (k : Expr) (values : List Nat) (j : Fin 3) (hk : k.eval values = j.val) :
    (sourceX t k).eval values = Encodable.encode (sourceCell t j).1 := by
  cases t <;> fin_cases j <;> simp [sourceX,sourceCell,Expr.eval,eqE,Op.eval,hk] <;> rfl

theorem sourceY_eval (t : Tromino) (k : Expr) (values : List Nat) (j : Fin 3) (hk : k.eval values = j.val) :
    (sourceY t k).eval values = Encodable.encode (sourceCell t j).2 := by
  cases t <;> fin_cases j <;> simp [sourceY,sourceCell,Expr.eval,eqE,Op.eval,hk] <;> rfl

theorem cellXY_eval (t : Tromino) (input : PeriodicStripTrominoPrefill) (front : List Nat)
    (i k : Expr) (index : Nat) (j : Fin 3) (hi : index < input.motif.length)
    (ei : i.eval (front ++ fields input) = index) (ek : k.eval (front ++ fields input) = j.val) :
    (cellX t front.length i k).eval (front ++ fields input) = (biasedCell t (bound input) input.motif[index] j).1 ∧
    (cellY t front.length i k).eval (front ++ fields input) = (biasedCell t (bound input) input.motif[index] j).2 := by
  have h0 := fieldExpr_eval input front i index 0 ei hi
  have h1 := fieldExpr_eval input front i index 1 ei hi
  have h2 := fieldExpr_eval input front i index 2 ei hi
  change (fieldExpr front.length i 0).eval (front ++ fields input) = CompletionStripEncoding.symmetryCode input.motif[index].symmetry at h0
  change (fieldExpr front.length i 1).eval (front ++ fields input) = Encodable.encode input.motif[index].offset.1 at h1
  change (fieldExpr front.length i 2).eval (front ++ fields input) = Encodable.encode input.motif[index].offset.2 at h2
  have hb := header_get input front 0 (by decide)
  simp only [Nat.add_zero] at hb
  simp only [cellX,cellY,eval_sub,eval_add,biased_eval,orientX_eval,orientY_eval,
    sourceX_eval t k _ j ek,sourceY_eval t k _ j ek,eval_var,hb,h0,h1,h2]
  exact ⟨rfl,rfl⟩

theorem cellX_noPower (t : Tromino) (depth : Nat) (i k : Expr)
    (hi : i.noPower = true) (hk : k.noPower = true) : (cellX t depth i k).noPower = true := by
  cases t <;> simp [cellX,fieldExpr,sourceX,sourceY,biased,orientX,negate,orE,eqE,Expr.noPower,hi,hk]

theorem cellY_noPower (t : Tromino) (depth : Nat) (i k : Expr)
    (hi : i.noPower = true) (hk : k.noPower = true) : (cellY t depth i k).noPower = true := by
  cases t <;> simp [cellY,fieldExpr,sourceX,sourceY,biased,orientY,negate,orE,eqE,Expr.noPower,hi,hk]

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw

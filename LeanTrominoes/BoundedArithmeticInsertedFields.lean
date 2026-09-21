/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic

/-! # Relocating arithmetic loads around inserted fields -/
namespace LeanTrominoes.BoundedArithmetic
open Expr

private def relocatedLoad (cut : Nat) (amount index : Expr) : Expr :=
  .ite (ltE index (.literal cut)) (.load index) (.load (index+amount))

def Expr.insertFields : Expr → Nat → Nat → Expr
  | .literal n,_,_ => .literal n
  | .load i,cut,amount => relocatedLoad cut (.literal amount) (i.insertFields cut amount)
  | .binary op a b,cut,amount => .binary op (a.insertFields cut amount) (b.insertFields cut amount)
  | .testBit a b,cut,amount => .testBit (a.insertFields cut amount) (b.insertFields cut amount)
  | .powerTwo a,cut,amount => .powerTwo (a.insertFields cut amount)
  | .ite t y n,cut,amount => .ite (t.insertFields cut amount) (y.insertFields cut amount) (n.insertFields cut amount)
  | .letE a b,cut,amount => .letE (a.insertFields cut amount) (b.insertFields (cut+1) amount)
  | .all n b,cut,amount => .all (n.insertFields cut amount) (b.insertFields (cut+1) amount)

def Expr.skipBlock : Expr → Nat → Expr
  | .literal n,_ => .literal n
  | .load i,cut => relocatedLoad cut (1+var cut) (i.skipBlock cut)
  | .binary op a b,cut => .binary op (a.skipBlock cut) (b.skipBlock cut)
  | .testBit a b,cut => .testBit (a.skipBlock cut) (b.skipBlock cut)
  | .powerTwo a,cut => .powerTwo (a.skipBlock cut)
  | .ite t y n,cut => .ite (t.skipBlock cut) (y.skipBlock cut) (n.skipBlock cut)
  | .letE a b,cut => .letE (a.skipBlock cut) (b.skipBlock (cut+1))
  | .all n b,cut => .all (n.skipBlock cut) (b.skipBlock (cut+1))

private theorem relocatedLoad_eval (leading block rest : List Nat) (amount index : Expr)
    (h : amount.eval (leading++block++rest)=block.length) :
    (relocatedLoad leading.length amount index).eval (leading++block++rest) =
      (leading++rest)[index.eval (leading++block++rest)]?.getD 0 := by
  simp only [relocatedLoad,Expr.eval,ltE,Op.eval,h]
  generalize index.eval (leading++block++rest) = i
  by_cases hi : i<leading.length
  · simp [hi,List.append_assoc,List.getElem?_append_left hi]
  · have lo : leading.length ≤ i := by omega
    have lo' : leading.length ≤ i+block.length := by omega
    have lo'' : block.length ≤ i+block.length-leading.length := by omega
    simp only [hi,if_false,ite_true,List.append_assoc,List.getElem?_append_right lo,
      List.getElem?_append_right lo',List.getElem?_append_right lo'']
    congr 2
    omega

theorem Expr.insertFields_eval (expr : Expr) (leading block rest : List Nat) :
    (expr.insertFields leading.length block.length).eval (leading++block++rest) = expr.eval (leading++rest) := by
  induction expr generalizing leading with
  | literal n => rfl
  | load i ih =>
    rw [Expr.insertFields,relocatedLoad_eval leading block rest (.literal block.length) (i.insertFields leading.length block.length) rfl,ih]
    rfl
  | binary op a b ia ib => simp only [Expr.insertFields,Expr.eval,ia,ib]
  | testBit a b ia ib => simp only [Expr.insertFields,Expr.eval,ia,ib]
  | powerTwo a ih => simp only [Expr.insertFields,Expr.eval,ih]
  | ite t y n it iy ino => simp only [Expr.insertFields,Expr.eval,it,iy,ino]
  | letE a b ia ib =>
    simp only [Expr.insertFields,Expr.eval,ia]
    exact ib (a.eval (leading++rest)::leading)
  | all n b ino ib =>
    simp only [Expr.insertFields,Expr.eval,ino]
    congr 2
    funext i
    rw [show (b.insertFields (leading.length+1) block.length).eval (i::(leading++block++rest)) =
      b.eval (i::(leading++rest)) from ib (i::leading)]

theorem Expr.skipBlock_eval (expr : Expr) (leading block rest : List Nat) :
    (expr.skipBlock leading.length).eval (leading++block.length::(block++rest)) = expr.eval (leading++rest) := by
  have amount (leading : List Nat) : (1+var leading.length : Expr).eval (leading++block.length::(block++rest)) =
      (block.length::block).length := by
    simp only [eval_add,eval_var,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem?_cons_zero,Option.getD_some,List.length_cons]
    change 1+block.length = block.length+1
    omega
  induction expr generalizing leading with
  | literal n => rfl
  | load i ih =>
    have h := relocatedLoad_eval leading (block.length::block) rest (1+var leading.length) (i.skipBlock leading.length) (by simpa using amount leading)
    simpa only [Expr.skipBlock,List.cons_append,List.append_assoc,ih,Expr.eval] using h
  | binary op a b ia ib => simp only [Expr.skipBlock,Expr.eval,ia,ib]
  | testBit a b ia ib => simp only [Expr.skipBlock,Expr.eval,ia,ib]
  | powerTwo a ih => simp only [Expr.skipBlock,Expr.eval,ih]
  | ite t y n it iy ino => simp only [Expr.skipBlock,Expr.eval,it,iy,ino]
  | letE a b ia ib =>
    simp only [Expr.skipBlock,Expr.eval,ia]
    exact ib (a.eval (leading++rest)::leading)
  | all n b ino ib =>
    simp only [Expr.skipBlock,Expr.eval,ino]
    congr 2
    funext i
    rw [show (b.skipBlock (leading.length+1)).eval (i::(leading++block.length::(block++rest))) =
      b.eval (i::(leading++rest)) from ib (i::leading)]

theorem Expr.insertFields_noPower (expr : Expr) (cut amount : Nat) :
    (expr.insertFields cut amount).noPower = expr.noPower := by
  induction expr generalizing cut <;> simp_all [Expr.insertFields,relocatedLoad,ltE,Expr.noPower,Bool.and_self]

theorem Expr.skipBlock_noPower (expr : Expr) (cut : Nat) : (expr.skipBlock cut).noPower = expr.noPower := by
  induction expr generalizing cut <;> simp_all [Expr.skipBlock,relocatedLoad,ltE,var,Expr.noPower,Bool.and_self]

end LeanTrominoes.BoundedArithmetic

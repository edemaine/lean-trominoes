/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BoundedArithmeticLogic

/-! # Fixed finite tables in the space-certified arithmetic language -/
namespace LeanTrominoes.BoundedArithmetic.Expr

def tableLookup (table : List (Nat × Nat)) (key : Expr) : Expr :=
  match table with
  | [] => 0
  | (k,v)::rest => .ite (eqE key (.literal k)) (.literal v) (tableLookup rest key)

theorem tableLookup_noPower (table : List (Nat × Nat)) (key : Expr)
    (allowed : key.noPower = true) : (tableLookup table key).noPower = true := by
  induction table with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨k,v⟩; simp [tableLookup,Expr.noPower,eqE,allowed,ih]

theorem tableLookup_encoded {A : Type} (items : List A) (encode value : A → Nat)
    (injective : Function.Injective encode) (key : Expr) (fields : List Nat)
    (a : A) (member : a ∈ items) (atKey : key.eval fields = encode a) :
    (tableLookup (items.map (fun b => (encode b,value b))) key).eval fields = value a := by
  induction items with
  | nil => simp at member
  | cons b rest ih =>
    by_cases same : a = b
    · subst a
      simp [tableLookup,Expr.eval,eqE,Op.eval,atKey]
    · have different : encode a ≠ encode b := fun h => same (injective h)
      have tail : a ∈ rest := (List.mem_cons.mp member).resolve_left same
      simp [tableLookup,Expr.eval,eqE,Op.eval,atKey,different,ih tail]

end LeanTrominoes.BoundedArithmetic.Expr

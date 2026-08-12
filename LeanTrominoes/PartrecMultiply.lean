import LeanTrominoes.PartrecFuel

/-!
# Explicit natural multiplication

The partial-recursive evaluator already has a fixed-width program that adds a
retained value to an accumulator.  This file uses it in a flat countdown to
compute a product while retaining only `[right, left, partialProduct]`.  The
construction is the forward arithmetic primitive needed to build standard
`Nat.pair` encodings.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- One fixed-width multiplication step. -/
def natMultiplyStepCode : Code := fuelAddPreviousCode

def natMultiplyStepList (values : List Nat) : List Nat :=
  [values[0]?.getD 0, values[1]?.getD 0,
    values[2]?.getD 0 + values[1]?.getD 0]

@[simp]
theorem natMultiplyStepCode_eval (values : List Nat) :
    natMultiplyStepCode.eval values =
      pure (natMultiplyStepList values) := by
  rw [natMultiplyStepCode]
  exact fuelAddPreviousCode_eval values

theorem natMultiplyStepList_iterate
    (steps marker left partialProduct : Nat) :
    (natMultiplyStepList^[steps]) [marker, left, partialProduct] =
      [marker, left, partialProduct + steps * left] := by
  induction steps with
  | zero => simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, natMultiplyStepList]
      ring

/-- Initialize the outer countdown and retained arithmetic payload. -/
def natMultiplyInputCode : Code :=
  prepend (get 1) <|
    prepend (get 1) <|
      prepend (get 0) zero

@[simp]
theorem natMultiplyInputCode_eval (left right : Nat) :
    natMultiplyInputCode.eval [left, right] =
      pure [right, right, left, 0] := by
  simp [natMultiplyInputCode]

/-- Binary code computing natural-number multiplication. -/
def natMultiplyCode : Code :=
  ((get 2).comp (flatIterate natMultiplyStepCode)).comp
    natMultiplyInputCode

@[simp]
theorem natMultiplyCode_eval (left right : Nat) :
    natMultiplyCode.eval [left, right] =
      pure [left * right] := by
  simp [natMultiplyCode, flatIterate_eval,
    natMultiplyStepList_iterate]
  ring

end Turing.ToPartrec.Code

import LeanTrominoes.PartrecAdd

/-!
# Explicit natural multiplication

The partial-recursive evaluator already has a fitted addition program.  This
file uses it in a flat countdown to compute a product while retaining only the
fixed-width payload `[left, partialProduct]`.  The construction is the forward
arithmetic primitive needed to build standard `Nat.pair` encodings.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- Arguments `[partialProduct, left]` for one repeated-addition step. -/
def natMultiplyStepArgumentsCode : Code :=
  prepend (get 1) (get 0)

@[simp]
theorem natMultiplyStepArgumentsCode_eval
    (left partialProduct : Nat) :
    natMultiplyStepArgumentsCode.eval [left, partialProduct] =
      pure [partialProduct, left] := by
  simp [natMultiplyStepArgumentsCode]

/-- Add the retained left factor to the partial product. -/
def natMultiplyStepSumCode : Code :=
  natAddCode.comp natMultiplyStepArgumentsCode

@[simp]
theorem natMultiplyStepSumCode_eval
    (left partialProduct : Nat) :
    natMultiplyStepSumCode.eval [left, partialProduct] =
      pure [partialProduct + left] := by
  simp [natMultiplyStepSumCode]

/-- One fixed-width multiplication step. -/
def natMultiplyStepCode : Code :=
  prepend (get 0) natMultiplyStepSumCode

def natMultiplyStepList (values : List Nat) : List Nat :=
  [values[0]?.getD 0,
    values[1]?.getD 0 + values[0]?.getD 0]

@[simp]
theorem natMultiplyStepCode_eval (values : List Nat) :
    natMultiplyStepCode.eval values =
      pure (natMultiplyStepList values) := by
  simp [natMultiplyStepCode, natMultiplyStepSumCode,
    natMultiplyStepArgumentsCode, natMultiplyStepList]

theorem natMultiplyStepList_iterate
    (steps left partialProduct : Nat) :
    (natMultiplyStepList^[steps]) [left, partialProduct] =
      [left, partialProduct + steps * left] := by
  induction steps with
  | zero => simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, natMultiplyStepList]
      ring

/-- Initialize the outer countdown with a zero partial product. -/
def natMultiplyInputCode : Code :=
  prepend (get 1) <|
    prepend (get 0) zero

@[simp]
theorem natMultiplyInputCode_eval (left right : Nat) :
    natMultiplyInputCode.eval [left, right] =
      pure [right, left, 0] := by
  simp [natMultiplyInputCode]

/-- Binary code computing natural-number multiplication. -/
def natMultiplyCode : Code :=
  (get 1).comp <|
    (flatIterate natMultiplyStepCode).comp natMultiplyInputCode

@[simp]
theorem natMultiplyCode_eval (left right : Nat) :
    natMultiplyCode.eval [left, right] =
      pure [left * right] := by
  simp [natMultiplyCode, flatIterate_eval,
    natMultiplyStepList_iterate]
  ring

end Turing.ToPartrec.Code

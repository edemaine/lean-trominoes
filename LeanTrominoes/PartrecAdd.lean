import LeanTrominoes.PartrecListCode

/-!
# Explicit partial-recursive natural addition

Natural addition is implemented as a flat countdown that repeatedly applies
successor to a singleton accumulator.  The fixed-width representation is
suited to later phase arithmetic inside streaming frontier checks.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

def natAddStepList (values : List Nat) : List Nat :=
  [values.headI + 1]

@[simp]
theorem succ_eval_natAddStep (values : List Nat) :
    succ.eval values = pure (natAddStepList values) := by
  simp [natAddStepList]

theorem natAddStepList_iterate
    (steps value : Nat) :
    (natAddStepList^[steps]) [value] =
      [value + steps] := by
  induction steps with
  | zero =>
      simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      simp [induction, natAddStepList]
      omega

/-- Reorder `[left, right]` into a countdown and accumulator. -/
def natAddInputCode : Code :=
  prepend (get 1) (get 0)

@[simp]
theorem natAddInputCode_eval (left right : Nat) :
    natAddInputCode.eval [left, right] =
      pure [right, left] := by
  simp [natAddInputCode]

/-- Binary explicit code computing natural addition. -/
def natAddCode : Code :=
  (flatIterate succ).comp natAddInputCode

@[simp]
theorem natAddCode_eval (left right : Nat) :
    natAddCode.eval [left, right] =
      pure [left + right] := by
  calc
    _ = (flatIterate succ).eval [right, left] := by
      simp [natAddCode]
    _ = pure ((natAddStepList^[right]) [left]) :=
      flatIterate_eval succ natAddStepList
        succ_eval_natAddStep right [left]
    _ = _ := by rw [natAddStepList_iterate]

end Turing.ToPartrec.Code

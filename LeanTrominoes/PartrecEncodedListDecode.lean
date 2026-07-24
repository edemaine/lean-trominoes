import LeanTrominoes.PartrecUnpair
import LeanTrominoes.PartrecSubtract

/-!
# Explicit views of standard encoded lists

Mathlib encodes the empty list as zero and a cons as

`Nat.succ (Nat.pair headCode tailCode)`.

The fixed-width view below turns either case into three native evaluator-list
fields.  Its tag is zero for nil and one for cons; the other two fields are
zero in the nil case and contain the encoded head and tail in the cons case.
-/

namespace Turing.ToPartrec.Code

/-- Native three-field view computed by `encodedListViewCode`. -/
def encodedListView (values : List Nat) : List Nat :=
  match values.headI with
  | 0 => [0, 0, 0]
  | constructorCode + 1 =>
      [1, constructorCode.unpair.1,
        constructorCode.unpair.2]

/-- Fixed-width view `[0, 0, 0]` of an encoded empty list. -/
def encodedListNilViewCode : Code :=
  prepend zero (prepend zero zero)

@[simp]
theorem encodedListNilViewCode_eval (values : List Nat) :
    encodedListNilViewCode.eval values =
      pure [0, 0, 0] := by
  simp [encodedListNilViewCode]

/-- Fixed-width view `[1, headCode, tailCode]` of an encoded cons. -/
def encodedListConsViewCode : Code :=
  prepend one (unpairCode.comp pred)

@[simp]
theorem encodedListConsViewCode_eval
    (headCode tailCode : Nat) :
    encodedListConsViewCode.eval
        [Nat.succ (Nat.pair headCode tailCode)] =
      pure [1, headCode, tailCode] := by
  simp [encodedListConsViewCode]

theorem encodedListConsViewCode_eval_at
    (constructorCode : Nat) (remaining : List Nat) :
    encodedListConsViewCode.eval
        (Nat.succ constructorCode :: remaining) =
      pure
        [1, constructorCode.unpair.1,
          constructorCode.unpair.2] := by
  simp [encodedListConsViewCode]

/-- Decode one constructor of a standard encoded list. -/
def encodedListViewCode : Code :=
  branchZero head encodedListNilViewCode
    encodedListConsViewCode

theorem encodedListViewCode_eval_values
    (values : List Nat) :
    encodedListViewCode.eval values =
      pure (encodedListView values) := by
  cases values with
  | nil =>
      exact
        branchZero_eval_zero_at head
          encodedListNilViewCode encodedListConsViewCode
          [] 0 (by simp) [0, 0, 0]
          (encodedListNilViewCode_eval []) rfl
  | cons value remaining =>
      cases value with
      | zero =>
          exact
            branchZero_eval_zero_at head
              encodedListNilViewCode encodedListConsViewCode
              (0 :: remaining) 0 (by simp) [0, 0, 0]
              (encodedListNilViewCode_eval (0 :: remaining))
              rfl
      | succ constructorCode =>
          simpa [encodedListViewCode, encodedListView] using
            branchZero_eval_succ_at head
              encodedListNilViewCode
              encodedListConsViewCode
              (Nat.succ constructorCode :: remaining)
              (Nat.succ constructorCode) (by simp)
              [1, constructorCode.unpair.1,
                constructorCode.unpair.2]
              (encodedListConsViewCode_eval_at
                constructorCode remaining)
              (Nat.succ_pos constructorCode)

@[simp]
theorem encodedListViewCode_eval
    {α : Type*} [Encodable α] (values : List α) :
    encodedListViewCode.eval [Encodable.encode values] =
      pure
        (match values with
        | [] => [0, 0, 0]
        | value :: remaining =>
            [1, Encodable.encode value,
              Encodable.encode remaining]) := by
  cases values with
  | nil =>
      simpa [encodedListView] using
        encodedListViewCode_eval_values [0]
  | cons value remaining =>
      simpa [encodedListView] using
        encodedListViewCode_eval_values
          [Encodable.encode (value :: remaining)]

/-- Replace the head field by the encoded tail of the encoded list it holds. -/
def encodedListTailStep (values : List Nat) : List Nat :=
  [(encodedListView values)[2]?.getD 0]

/-- One tail step, expressed through the fixed-width list view. -/
def encodedListTailStepCode : Code :=
  (get 2).comp encodedListViewCode

@[simp]
theorem encodedListTailStepCode_eval
    (values : List Nat) :
    encodedListTailStepCode.eval values =
      pure (encodedListTailStep values) := by
  simp [encodedListTailStepCode,
    encodedListTailStep, encodedListViewCode_eval_values]

@[simp]
theorem encodedListTailStep_encode
    {α : Type*} [Encodable α] (values : List α) :
    encodedListTailStep [Encodable.encode values] =
      [Encodable.encode values.tail] := by
  cases values <;> simp [encodedListTailStep,
    encodedListView]

theorem encodedListTailStep_iterate
    {α : Type*} [Encodable α]
    (steps : Nat) (values : List α) :
    ((encodedListTailStep)^[steps])
        [Encodable.encode values] =
      [Encodable.encode (values.drop steps)] := by
  induction steps generalizing values with
  | zero =>
      simp
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      simp only [encodedListTailStep_encode]
      simpa using induction values.tail

theorem length_le_encode
    {α : Type*} [Encodable α] (values : List α) :
    values.length ≤ Encodable.encode values := by
  induction values with
  | nil =>
      simp
  | cons value remaining induction =>
      simp only [List.length_cons,
        Encodable.encode_list_cons, Nat.succ_le_succ_iff]
      exact induction.trans
        (Nat.right_le_pair
          (Encodable.encode value)
          (Encodable.encode remaining))

/-- Exhaust an encoded list using its own code as a safe tail-step count. -/
def encodedListExhaustCode : Code :=
  flatIterate encodedListTailStepCode

@[simp]
theorem encodedListExhaustCode_eval
    {α : Type*} [Encodable α] (values : List α) :
    encodedListExhaustCode.eval
        [Encodable.encode values, Encodable.encode values] =
      pure [0] := by
  calc
    _ = pure
        (((encodedListTailStep)^[
          Encodable.encode values])
          [Encodable.encode values]) :=
      flatIterate_eval encodedListTailStepCode
        encodedListTailStep
        encodedListTailStepCode_eval
        (Encodable.encode values)
        [Encodable.encode values]
    _ = pure
        [Encodable.encode
          (values.drop (Encodable.encode values))] := by
      rw [encodedListTailStep_iterate]
    _ = pure [0] := by
      rw [List.drop_eq_nil_of_le (length_le_encode values)]
      simp

end Turing.ToPartrec.Code

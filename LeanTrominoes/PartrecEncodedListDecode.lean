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

/-- Decode one constructor of a standard encoded list. -/
def encodedListViewCode : Code :=
  branchZero head encodedListNilViewCode
    encodedListConsViewCode

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
      exact
        branchZero_eval_zero_at head
          encodedListNilViewCode encodedListConsViewCode
          [0] 0 (by simp) [0, 0, 0]
          (encodedListNilViewCode_eval [0]) rfl
  | cons value remaining =>
      simpa [encodedListViewCode] using
        branchZero_eval_succ_at head
          encodedListNilViewCode encodedListConsViewCode
          [Encodable.encode (value :: remaining)]
          (Encodable.encode (value :: remaining))
          (by simp)
          [1, Encodable.encode value,
            Encodable.encode remaining]
          (by simp)
          (by simp)

end Turing.ToPartrec.Code

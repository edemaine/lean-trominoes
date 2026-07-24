import LeanTrominoes.PartrecEncodedListDecode
import LeanTrominoes.PartrecUnpairSpace
import LeanTrominoes.PartrecSubtractSpace

/-!
# Evaluator-space certificate for encoded-list views

The nil branch constructs three zero fields.  The cons branch takes one
predecessor, unpairs the constructor payload, and prepends the nonempty tag.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec

namespace EvaluatorCodeFits

def encodedListNilTailCost (values : List Nat) : Nat :=
  prependCost values [0] [0]
    (zeroCost values) (zeroCost values)

theorem encodedListNilTail (values : List Nat) :
    EvaluatorCodeFits
      (Code.prepend Code.zero Code.zero)
      values [0, 0]
      (encodedListNilTailCost values) := by
  simpa [encodedListNilTailCost, prependCost] using
    prepend (zero values) (zero values)

def encodedListNilViewCost (values : List Nat) : Nat :=
  prependCost values [0] [0, 0]
    (zeroCost values)
    (encodedListNilTailCost values)

theorem encodedListNilView (values : List Nat) :
    EvaluatorCodeFits Code.encodedListNilViewCode
      values [0, 0, 0]
      (encodedListNilViewCost values) := by
  simpa [Code.encodedListNilViewCode,
    encodedListNilViewCost, prependCost] using
    prepend (zero values) (encodedListNilTail values)

def encodedListConsTailCost
    (headCode tailCode : Nat) : Nat :=
  unpairCost (Nat.pair headCode tailCode) +
    predCost
      [Nat.succ (Nat.pair headCode tailCode)]

theorem encodedListConsTail
    (headCode tailCode : Nat) :
    EvaluatorCodeFits
      (Code.unpairCode.comp Code.pred)
      [Nat.succ (Nat.pair headCode tailCode)]
      [headCode, tailCode]
      (encodedListConsTailCost headCode tailCode) := by
  simpa [encodedListConsTailCost,
    Code.subtractStepList] using
    comp
      (unpair (Nat.pair headCode tailCode))
      (pred_named
        [Nat.succ (Nat.pair headCode tailCode)])

def encodedListConsViewCost
    (headCode tailCode : Nat) : Nat :=
  prependCost
    [Nat.succ (Nat.pair headCode tailCode)]
    [1] [headCode, tailCode]
    (oneCost
      [Nat.succ (Nat.pair headCode tailCode)])
    (encodedListConsTailCost headCode tailCode)

theorem encodedListConsView
    (headCode tailCode : Nat) :
    EvaluatorCodeFits Code.encodedListConsViewCode
      [Nat.succ (Nat.pair headCode tailCode)]
      [1, headCode, tailCode]
      (encodedListConsViewCost headCode tailCode) := by
  simpa [Code.encodedListConsViewCode,
    encodedListConsViewCost, prependCost] using
    prepend
      (one [Nat.succ (Nat.pair headCode tailCode)])
      (encodedListConsTail headCode tailCode)

def encodedListViewCost
    {α : Type*} [Encodable α] (values : List α) : Nat :=
  match values with
  | [] =>
      branchZeroZeroCost [0] [0, 0, 0] 0
        (headCost [0])
        (encodedListNilViewCost [0])
  | value :: remaining =>
      let listCode := Encodable.encode (value :: remaining)
      branchZeroSuccCost [listCode]
        [1, Encodable.encode value,
          Encodable.encode remaining]
        listCode (headCost [listCode])
        (encodedListConsViewCost
          (Encodable.encode value)
          (Encodable.encode remaining))

theorem encodedListView
    {α : Type*} [Encodable α] (values : List α) :
    EvaluatorCodeFits Code.encodedListViewCode
      [Encodable.encode values]
      (match values with
      | [] => [0, 0, 0]
      | value :: remaining =>
          [1, Encodable.encode value,
            Encodable.encode remaining])
      (encodedListViewCost values) := by
  cases values with
  | nil =>
      simpa [Code.encodedListViewCode,
        encodedListViewCost] using
        branchZero_zero rfl
          (head [0])
          (encodedListNilView [0])
  | cons value remaining =>
      have positive :
          0 < Encodable.encode (value :: remaining) := by
        simp
      simpa [Code.encodedListViewCode,
        encodedListViewCost] using
        branchZero_succ positive
          (head
            [Encodable.encode (value :: remaining)])
          (encodedListConsView
            (Encodable.encode value)
            (Encodable.encode remaining))

end EvaluatorCodeFits

end PartrecToTM2
end Turing

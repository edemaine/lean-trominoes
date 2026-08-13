/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

def encodedListConsTailAtCost
    (headCode tailCode : Nat)
    (remaining : List Nat) : Nat :=
  unpairCost (Nat.pair headCode tailCode) +
    predCost
      (Nat.succ (Nat.pair headCode tailCode) ::
        remaining)

theorem encodedListConsTailAt
    (headCode tailCode : Nat)
    (remaining : List Nat) :
    EvaluatorCodeFits
      (Code.unpairCode.comp Code.pred)
      (Nat.succ (Nat.pair headCode tailCode) ::
        remaining)
      [headCode, tailCode]
      (encodedListConsTailAtCost
        headCode tailCode remaining) := by
  simpa [encodedListConsTailAtCost,
    Code.subtractStepList] using
    comp
      (unpair (Nat.pair headCode tailCode))
      (pred_named
        (Nat.succ (Nat.pair headCode tailCode) ::
          remaining))

def encodedListConsTailCost
    (headCode tailCode : Nat) : Nat :=
  encodedListConsTailAtCost headCode tailCode []

theorem encodedListConsTail
    (headCode tailCode : Nat) :
    EvaluatorCodeFits
      (Code.unpairCode.comp Code.pred)
      [Nat.succ (Nat.pair headCode tailCode)]
      [headCode, tailCode]
      (encodedListConsTailCost headCode tailCode) := by
  simpa [encodedListConsTailCost] using
    encodedListConsTailAt headCode tailCode []

def encodedListConsViewAtCost
    (headCode tailCode : Nat)
    (remaining : List Nat) : Nat :=
  prependCost
    (Nat.succ (Nat.pair headCode tailCode) ::
      remaining)
    [1] [headCode, tailCode]
    (oneCost
      (Nat.succ (Nat.pair headCode tailCode) ::
        remaining))
    (encodedListConsTailAtCost
      headCode tailCode remaining)

theorem encodedListConsViewAt
    (headCode tailCode : Nat)
    (remaining : List Nat) :
    EvaluatorCodeFits Code.encodedListConsViewCode
      (Nat.succ (Nat.pair headCode tailCode) ::
        remaining)
      [1, headCode, tailCode]
      (encodedListConsViewAtCost
        headCode tailCode remaining) := by
  simpa [Code.encodedListConsViewCode,
    encodedListConsViewAtCost, prependCost] using
    prepend
      (one
        (Nat.succ (Nat.pair headCode tailCode) ::
          remaining))
      (encodedListConsTailAt
        headCode tailCode remaining)

def encodedListConsViewCost
    (headCode tailCode : Nat) : Nat :=
  encodedListConsViewAtCost headCode tailCode []

theorem encodedListConsView
    (headCode tailCode : Nat) :
    EvaluatorCodeFits Code.encodedListConsViewCode
      [Nat.succ (Nat.pair headCode tailCode)]
      [1, headCode, tailCode]
      (encodedListConsViewCost headCode tailCode) := by
  simpa [encodedListConsViewCost] using
    encodedListConsViewAt headCode tailCode []

def encodedListViewValuesCost
    (values : List Nat) : Nat :=
  match values.headI with
  | 0 =>
      branchZeroZeroCost values [0, 0, 0] 0
        (headCost values)
        (encodedListNilViewCost values)
  | constructorCode + 1 =>
      branchZeroSuccCost values
        [1, constructorCode.unpair.1,
          constructorCode.unpair.2]
        (constructorCode + 1)
        (headCost values)
        (encodedListConsViewAtCost
          constructorCode.unpair.1
          constructorCode.unpair.2 values.tail)

theorem encodedListViewValues
    (values : List Nat) :
    EvaluatorCodeFits Code.encodedListViewCode
      values (Code.encodedListView values)
      (encodedListViewValuesCost values) := by
  cases values with
  | nil =>
      simpa [Code.encodedListViewCode,
        Code.encodedListView,
        encodedListViewValuesCost] using
        branchZero_zero rfl
          (head [])
          (encodedListNilView [])
  | cons value remaining =>
      cases value with
      | zero =>
          simpa [Code.encodedListViewCode,
            Code.encodedListView,
            encodedListViewValuesCost] using
            branchZero_zero rfl
              (head (0 :: remaining))
              (encodedListNilView (0 :: remaining))
      | succ constructorCode =>
          have positive :
              0 < Nat.succ constructorCode :=
            Nat.succ_pos constructorCode
          have consView :
              EvaluatorCodeFits
                Code.encodedListConsViewCode
                (Nat.succ constructorCode :: remaining)
                [1, constructorCode.unpair.1,
                  constructorCode.unpair.2]
                (encodedListConsViewAtCost
                  constructorCode.unpair.1
                  constructorCode.unpair.2
                  remaining) := by
            simpa using
              encodedListConsViewAt
                constructorCode.unpair.1
                constructorCode.unpair.2
                remaining
          simpa [Code.encodedListViewCode,
            Code.encodedListView,
            encodedListViewValuesCost] using
            branchZero_succ positive
              (head
                (Nat.succ constructorCode ::
                  remaining))
              consView

def encodedListTailStepCost
    (values : List Nat) : Nat :=
  getCost 2 (Code.encodedListView values) +
    encodedListViewValuesCost values

theorem encodedListTailStep
    (values : List Nat) :
    EvaluatorCodeFits Code.encodedListTailStepCode
      values (Code.encodedListTailStep values)
      (encodedListTailStepCost values) := by
  simpa [Code.encodedListTailStepCode,
    Code.encodedListTailStep,
    encodedListTailStepCost] using
    comp
      (get 2 (Code.encodedListView values))
      (encodedListViewValues values)

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

theorem encodedListViewCost_le_linear
    {α : Type*} [Encodable α] (values : List α) :
    encodedListViewCost values ≤
      2000000000 *
        (encodedListSpace
          [2 * Encodable.encode values + 4] + 1) := by
  cases values with
  | nil =>
      have zeroBits :
          (Computability.encodeNat 0).length = 0 := rfl
      have oneBits :
          (Computability.encodeNat 1).length = 1 := rfl
      have fourBits :
          (Computability.encodeNat 4).length = 3 := rfl
      simp [encodedListViewCost,
        encodedListNilViewCost, encodedListNilTailCost,
        branchZeroZeroCost, branchZeroTestCost,
        prependCost, idCost,
        headCost, nilCost, zeroCost,
        zeroPrimeCost, tailCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits, fourBits]
  | cons value remaining =>
      let headCode := Encodable.encode value
      let tailCode := Encodable.encode remaining
      let constructorCode := Nat.pair headCode tailCode
      let listCode := Nat.succ constructorCode
      let limit := 2 * listCode + 4
      have constructorBound : constructorCode ≤ limit := by
        simp only [constructorCode, limit, listCode]
        omega
      have headBound : headCode ≤ limit :=
        (Nat.left_le_pair headCode tailCode).trans
          constructorBound
      have tailBound : tailCode ≤ limit :=
        (Nat.right_le_pair headCode tailCode).trans
          constructorBound
      have listBound : listCode ≤ limit := by
        simp only [limit]
        omega
      have listSuccBound : listCode + 1 ≤ limit := by
        simp only [limit]
        omega
      have constructorBits :=
        encodeNat_length_mono constructorBound
      have headBits := encodeNat_length_mono headBound
      have tailBits := encodeNat_length_mono tailBound
      have listBits := encodeNat_length_mono listBound
      have listSuccBits :=
        encodeNat_length_mono listSuccBound
      have unpairBound :=
        unpairCost_le_linear constructorCode
      have unpairLimit :
          encodedListSpace [2 * constructorCode + 4] ≤
            encodedListSpace [limit] := by
        have numeric :
            2 * constructorCode + 4 ≤ limit := by
          simp only [limit, listCode]
          omega
        simpa only [encodedListSpace_cons,
          encodedListSpace_nil, Nat.add_le_add_iff_right] using
          encodeNat_length_mono numeric
      have zeroBits :
          (Computability.encodeNat 0).length = 0 := rfl
      have oneBits :
          (Computability.encodeNat 1).length = 1 := rfl
      change
        encodedListViewCost (value :: remaining) ≤
          2000000000 *
            (encodedListSpace [limit] + 1)
      simp [encodedListViewCost,
        encodedListConsViewCost,
        encodedListConsViewAtCost,
        encodedListConsTailAtCost,
        predCost, branchZeroSuccCost,
        branchZeroTestCost,
        prependCost, idCost,
        headCost, nilCost, oneCost, zeroCost,
        zeroPrimeCost, tailCost, succCost,
        Code.subtractStepList,
        encodedListSpace_cons, encodedListSpace_nil,
        headCode, tailCode, constructorCode,
        listCode, limit, zeroBits, oneBits] at *
      omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing

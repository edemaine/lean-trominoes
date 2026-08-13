/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecDiv2Parity
import LeanTrominoes.PartrecUnpair
import LeanTrominoes.Tiling

/-!
# Explicit decoding of encoded lattice cells

Mathlib encodes a nonnegative integer `n` as `2n` and a negative integer
`-(n+1)` as `2n+1`.  Thus division by two exposes a magnitude and the low bit
is exactly a sign tag.  Combining this observation with standard unpairing
gives a fixed four-field view of an encoded lattice cell.
-/

namespace LeanTrominoes

namespace IntEncoding

/-- Natural payload in Mathlib's standard integer encoding. -/
def magnitude : Int → Nat
  | .ofNat value => value
  | .negSucc value => value

/-- Zero for nonnegative integers and one for negative integers. -/
def sign : Int → Nat
  | .ofNat _ => 0
  | .negSucc _ => 1

@[simp]
theorem encode_ofNat (value : Nat) :
    Encodable.encode (Int.ofNat value) = 2 * value := by
  rfl

@[simp]
theorem encode_negSucc (value : Nat) :
    Encodable.encode (Int.negSucc value) =
      2 * value + 1 := by
  rfl

@[simp]
theorem encode_div2 (value : Int) :
    (Encodable.encode value).div2 =
      magnitude value := by
  cases value with
  | ofNat natural =>
      change (2 * natural).div2 = natural
      simp
  | negSucc natural =>
      change (2 * natural + 1).div2 = natural
      simp

@[simp]
theorem encode_bodd (value : Int) :
    (Encodable.encode value).bodd.toNat =
      sign value := by
  cases value with
  | ofNat natural =>
      change (2 * natural).bodd.toNat = 0
      simp
  | negSucc natural =>
      change (2 * natural + 1).bodd.toNat = 1
      simp

theorem sign_eq_zero_iff (value : Int) :
    sign value = 0 ↔ 0 ≤ value := by
  cases value <;> simp [sign]

end IntEncoding

end LeanTrominoes

namespace Turing.ToPartrec.Code

open LeanTrominoes

/-- Decode the integer code stored at a fixed native-list offset. -/
def intViewAtCode (index : Nat) : Code :=
  div2ParityCode.comp (get index)

/-- Select the magnitude from a decoded integer field. -/
def intMagnitudeAtCode (index : Nat) : Code :=
  (get 0).comp (intViewAtCode index)

/-- Select the sign tag from a decoded integer field. -/
def intSignAtCode (index : Nat) : Code :=
  (get 1).comp (intViewAtCode index)

@[simp]
theorem intViewAtCode_eval
    (index : Nat) (values : List Nat) :
    (intViewAtCode index).eval values =
      pure
        [(values[index]?.getD 0).div2,
          (values[index]?.getD 0).bodd.toNat] := by
  simp [intViewAtCode]

@[simp]
theorem intMagnitudeAtCode_eval
    (index : Nat) (values : List Nat) :
    (intMagnitudeAtCode index).eval values =
      pure [(values[index]?.getD 0).div2] := by
  simp [intMagnitudeAtCode]

@[simp]
theorem intSignAtCode_eval
    (index : Nat) (values : List Nat) :
    (intSignAtCode index).eval values =
      pure [(values[index]?.getD 0).bodd.toNat] := by
  simp [intSignAtCode]

/-- Convert `[xCode, yCode]` into
`[xMagnitude, xSign, yMagnitude, ySign]`. -/
def cellFieldsCode : Code :=
  prepend (intMagnitudeAtCode 0) <|
    prepend (intSignAtCode 0) <|
      prepend (intMagnitudeAtCode 1) <|
        intSignAtCode 1

@[simp]
theorem cellFieldsCode_eval (x y : Int) :
    cellFieldsCode.eval
        [Encodable.encode x, Encodable.encode y] =
      pure
        [IntEncoding.magnitude x, IntEncoding.sign x,
          IntEncoding.magnitude y, IntEncoding.sign y] := by
  simp [cellFieldsCode]

/-- Unary fixed-width decoder for the standard encoding of `Cell`. -/
def cellViewCode : Code :=
  cellFieldsCode.comp unpairCode

@[simp]
theorem cellViewCode_eval (cell : Cell) :
    cellViewCode.eval [Encodable.encode cell] =
      pure
        [IntEncoding.magnitude cell.1,
          IntEncoding.sign cell.1,
          IntEncoding.magnitude cell.2,
          IntEncoding.sign cell.2] := by
  rcases cell with ⟨x, y⟩
  simp [cellViewCode]

end Turing.ToPartrec.Code

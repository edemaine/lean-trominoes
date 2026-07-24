import LeanTrominoes.PartrecCellDecode
import LeanTrominoes.PartrecDiv2ParitySpace
import LeanTrominoes.PartrecUnpairSpace

/-!
# Evaluator-space certificate for encoded-cell decoding

The certificate unpairs a cell code, runs the fitted quotient/parity decoder
on each coordinate code, and selects the four fixed output fields.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def intViewAtCost
    (index : Nat) (values : List Nat) : Nat :=
  div2ParityCost (values[index]?.getD 0) +
    getCost index values

theorem intViewAt
    (index : Nat) (values : List Nat) :
    EvaluatorCodeFits (Code.intViewAtCode index)
      values
      [(values[index]?.getD 0).div2,
        (values[index]?.getD 0).bodd.toNat]
      (intViewAtCost index values) := by
  simpa [Code.intViewAtCode,
    intViewAtCost] using
    comp
      (div2Parity (values[index]?.getD 0))
      (get index values)

def intMagnitudeAtCost
    (index : Nat) (values : List Nat) : Nat :=
  getCost 0
      [(values[index]?.getD 0).div2,
        (values[index]?.getD 0).bodd.toNat] +
    intViewAtCost index values

theorem intMagnitudeAt
    (index : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.intMagnitudeAtCode index) values
      [(values[index]?.getD 0).div2]
      (intMagnitudeAtCost index values) := by
  simpa [Code.intMagnitudeAtCode,
    intMagnitudeAtCost] using
    comp
      (get 0
        [(values[index]?.getD 0).div2,
          (values[index]?.getD 0).bodd.toNat])
      (intViewAt index values)

def intSignAtCost
    (index : Nat) (values : List Nat) : Nat :=
  getCost 1
      [(values[index]?.getD 0).div2,
        (values[index]?.getD 0).bodd.toNat] +
    intViewAtCost index values

theorem intSignAt
    (index : Nat) (values : List Nat) :
    EvaluatorCodeFits
      (Code.intSignAtCode index) values
      [(values[index]?.getD 0).bodd.toNat]
      (intSignAtCost index values) := by
  simpa [Code.intSignAtCode,
    intSignAtCost] using
    comp
      (get 1
        [(values[index]?.getD 0).div2,
          (values[index]?.getD 0).bodd.toNat])
      (intViewAt index values)

def cellYFieldsCost
    (xCode yCode : Nat) : Nat :=
  let values := [xCode, yCode]
  prependCost values [yCode.div2]
    [yCode.bodd.toNat]
    (intMagnitudeAtCost 1 values)
    (intSignAtCost 1 values)

theorem cellYFields
    (xCode yCode : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.intMagnitudeAtCode 1)
        (Code.intSignAtCode 1))
      [xCode, yCode]
      [yCode.div2, yCode.bodd.toNat]
      (cellYFieldsCost xCode yCode) := by
  simpa [cellYFieldsCost, prependCost] using
    prepend
      (intMagnitudeAt 1 [xCode, yCode])
      (intSignAt 1 [xCode, yCode])

def cellSignAndYCost
    (xCode yCode : Nat) : Nat :=
  let values := [xCode, yCode]
  prependCost values [xCode.bodd.toNat]
    [yCode.div2, yCode.bodd.toNat]
    (intSignAtCost 0 values)
    (cellYFieldsCost xCode yCode)

theorem cellSignAndY
    (xCode yCode : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.intSignAtCode 0)
        (Code.prepend
          (Code.intMagnitudeAtCode 1)
          (Code.intSignAtCode 1)))
      [xCode, yCode]
      [xCode.bodd.toNat,
        yCode.div2, yCode.bodd.toNat]
      (cellSignAndYCost xCode yCode) := by
  simpa [cellSignAndYCost, prependCost] using
    prepend
      (intSignAt 0 [xCode, yCode])
      (cellYFields xCode yCode)

def cellFieldsCost
    (xCode yCode : Nat) : Nat :=
  let values := [xCode, yCode]
  prependCost values [xCode.div2]
    [xCode.bodd.toNat,
      yCode.div2, yCode.bodd.toNat]
    (intMagnitudeAtCost 0 values)
    (cellSignAndYCost xCode yCode)

theorem cellFields
    (xCode yCode : Nat) :
    EvaluatorCodeFits Code.cellFieldsCode
      [xCode, yCode]
      [xCode.div2, xCode.bodd.toNat,
        yCode.div2, yCode.bodd.toNat]
      (cellFieldsCost xCode yCode) := by
  simpa [Code.cellFieldsCode,
    cellFieldsCost, prependCost] using
    prepend
      (intMagnitudeAt 0 [xCode, yCode])
      (cellSignAndY xCode yCode)

def cellViewCost (cell : Cell) : Nat :=
  cellFieldsCost
      (Encodable.encode cell.1)
      (Encodable.encode cell.2) +
    unpairCost (Encodable.encode cell)

theorem cellView (cell : Cell) :
    EvaluatorCodeFits Code.cellViewCode
      [Encodable.encode cell]
      [IntEncoding.magnitude cell.1,
        IntEncoding.sign cell.1,
        IntEncoding.magnitude cell.2,
        IntEncoding.sign cell.2]
      (cellViewCost cell) := by
  rcases cell with ⟨x, y⟩
  have outer :
      EvaluatorCodeFits Code.unpairCode
        [Nat.pair (Encodable.encode x)
          (Encodable.encode y)]
        [Encodable.encode x, Encodable.encode y]
        (unpairCost
          (Nat.pair (Encodable.encode x)
            (Encodable.encode y))) := by
    simpa using
      unpair
        (Nat.pair (Encodable.encode x)
          (Encodable.encode y))
  simpa [Code.cellViewCode, cellViewCost] using
    comp
      (cellFields
        (Encodable.encode x)
        (Encodable.encode y))
      outer

theorem cellViewCost_le_linear (cell : Cell) :
    cellViewCost cell ≤
      12000000000 *
        (encodedListSpace
          [2 * Encodable.encode cell + 4] + 1) := by
  rcases cell with ⟨x, y⟩
  let xCode := Encodable.encode x
  let yCode := Encodable.encode y
  let cellCode := Nat.pair xCode yCode
  let limit := 2 * cellCode + 4
  have cellBound : cellCode ≤ limit := by
    simp only [limit]
    omega
  have xBound : xCode ≤ limit :=
    (Nat.left_le_pair xCode yCode).trans cellBound
  have yBound : yCode ≤ limit :=
    (Nat.right_le_pair xCode yCode).trans cellBound
  have xDivBound : xCode.div2 ≤ limit := by
    have identity := Nat.bodd_add_div2 xCode
    omega
  have yDivBound : yCode.div2 ≤ limit := by
    have identity := Nat.bodd_add_div2 yCode
    omega
  have xSignBound : xCode.bodd.toNat ≤ limit := by
    cases xCode.bodd <;> simp [limit]
  have ySignBound : yCode.bodd.toNat ≤ limit := by
    cases yCode.bodd <;> simp [limit]
  have cellBits := encodeNat_length_mono cellBound
  have xBits := encodeNat_length_mono xBound
  have yBits := encodeNat_length_mono yBound
  have xDivBits := encodeNat_length_mono xDivBound
  have yDivBits := encodeNat_length_mono yDivBound
  have xSignBits := encodeNat_length_mono xSignBound
  have ySignBits := encodeNat_length_mono ySignBound
  have xSuccBits :=
    encodeNat_length_mono
      (show xCode + 1 ≤ limit by
        have pairBound := Nat.left_le_pair xCode yCode
        simp only [limit, cellCode]
        omega)
  have ySuccBits :=
    encodeNat_length_mono
      (show yCode + 1 ≤ limit by
        have pairBound := Nat.right_le_pair xCode yCode
        simp only [limit, cellCode]
        omega)
  have xDivSuccBits :=
    encodeNat_length_mono
      (show xCode.div2 + 1 ≤ limit by
        have identity := Nat.bodd_add_div2 xCode
        omega)
  have yDivSuccBits :=
    encodeNat_length_mono
      (show yCode.div2 + 1 ≤ limit by
        have identity := Nat.bodd_add_div2 yCode
        omega)
  have xSignSuccBits :=
    encodeNat_length_mono
      (show xCode.bodd.toNat + 1 ≤ limit by
        cases xCode.bodd <;> simp [limit])
  have ySignSuccBits :=
    encodeNat_length_mono
      (show yCode.bodd.toNat + 1 ≤ limit by
        cases yCode.bodd <;> simp [limit])
  have unpairBound := unpairCost_le_linear cellCode
  have unpairLimit :
      encodedListSpace [2 * cellCode + 4] =
        encodedListSpace [limit] := by
    rfl
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  change
    cellViewCost (x, y) ≤
      12000000000 *
        (encodedListSpace [limit] + 1)
  simp [cellViewCost, cellFieldsCost,
    cellSignAndYCost, cellYFieldsCost,
    intMagnitudeAtCost, intSignAtCost,
    intViewAtCost, div2ParityCost, binaryDiv2Cost,
    prependCost, getCost, dropCost, idCost,
    headCost, nilCost,
    zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    xCode, yCode, cellCode, limit,
    zeroBits, oneBits] at *
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing

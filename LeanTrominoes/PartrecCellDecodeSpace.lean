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

end EvaluatorCodeFits

end PartrecToTM2
end Turing

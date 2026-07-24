import LeanTrominoes.PartrecStripCellBounds
import LeanTrominoes.PartrecCellDecodeSpace
import LeanTrominoes.PartrecNatCompareSpace

/-!
# Evaluator-space certificate for one strip-cell bounds test

The certificate composes the fitted cell decoder, fixed-field projections,
zero-sign tests, natural upper-bound comparisons, and three short-circuiting
conjunctions.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def stripCellViewCost
    (width period : Nat) (cell : Cell) : Nat :=
  cellViewCost cell +
    getCost 2
      [width, period, Encodable.encode cell]

theorem stripCellView
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellViewCode
      [width, period, Encodable.encode cell]
      [IntEncoding.magnitude cell.1,
        IntEncoding.sign cell.1,
        IntEncoding.magnitude cell.2,
        IntEncoding.sign cell.2]
      (stripCellViewCost width period cell) := by
  simpa [Code.stripCellViewCode,
    stripCellViewCost] using
    comp (cellView cell)
      (get 2
        [width, period, Encodable.encode cell])

def stripCellFieldCost
    (field width period : Nat) (cell : Cell) : Nat :=
  getCost field
      [IntEncoding.magnitude cell.1,
        IntEncoding.sign cell.1,
        IntEncoding.magnitude cell.2,
        IntEncoding.sign cell.2] +
    stripCellViewCost width period cell

theorem stripCellField
    (field width period : Nat) (cell : Cell) :
    EvaluatorCodeFits (Code.stripCellFieldCode field)
      [width, period, Encodable.encode cell]
      [[IntEncoding.magnitude cell.1,
          IntEncoding.sign cell.1,
          IntEncoding.magnitude cell.2,
          IntEncoding.sign cell.2][field]?.getD 0]
      (stripCellFieldCost field width period cell) := by
  simpa [Code.stripCellFieldCode,
    stripCellFieldCost] using
    comp
      (get field
        [IntEncoding.magnitude cell.1,
          IntEncoding.sign cell.1,
          IntEncoding.magnitude cell.2,
          IntEncoding.sign cell.2])
      (stripCellView width period cell)

def stripCellXNonnegativeCost
    (width period : Nat) (cell : Cell) : Nat :=
  isZeroCost
    [width, period, Encodable.encode cell]
    (IntEncoding.sign cell.1)
    (stripCellFieldCost 1 width period cell)

theorem stripCellXNonnegative
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellXNonnegativeCode
      [width, period, Encodable.encode cell]
      [if IntEncoding.sign cell.1 = 0 then 1 else 0]
      (stripCellXNonnegativeCost width period cell) := by
  simpa [Code.stripCellXNonnegativeCode,
    stripCellXNonnegativeCost] using
    isZero (stripCellField 1 width period cell)

def stripCellYNonnegativeCost
    (width period : Nat) (cell : Cell) : Nat :=
  isZeroCost
    [width, period, Encodable.encode cell]
    (IntEncoding.sign cell.2)
    (stripCellFieldCost 3 width period cell)

theorem stripCellYNonnegative
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellYNonnegativeCode
      [width, period, Encodable.encode cell]
      [if IntEncoding.sign cell.2 = 0 then 1 else 0]
      (stripCellYNonnegativeCost width period cell) := by
  simpa [Code.stripCellYNonnegativeCode,
    stripCellYNonnegativeCost] using
    isZero (stripCellField 3 width period cell)

def stripCellXUpperArgumentsCost
    (width period : Nat) (cell : Cell) : Nat :=
  prependCost
    [width, period, Encodable.encode cell]
    [IntEncoding.magnitude cell.1] [period]
    (stripCellFieldCost 0 width period cell)
    (getCost 1
      [width, period, Encodable.encode cell])

theorem stripCellXUpperArguments
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellXUpperArgumentsCode
      [width, period, Encodable.encode cell]
      [IntEncoding.magnitude cell.1, period]
      (stripCellXUpperArgumentsCost
        width period cell) := by
  simpa [Code.stripCellXUpperArgumentsCode,
    stripCellXUpperArgumentsCost, prependCost] using
    prepend
      (stripCellField 0 width period cell)
      (get 1
        [width, period, Encodable.encode cell])

def stripCellXUpperCost
    (width period : Nat) (cell : Cell) : Nat :=
  natLtCost (IntEncoding.magnitude cell.1) period +
    stripCellXUpperArgumentsCost width period cell

theorem stripCellXUpper
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellXUpperCode
      [width, period, Encodable.encode cell]
      [if IntEncoding.magnitude cell.1 < period
        then 1 else 0]
      (stripCellXUpperCost width period cell) := by
  simpa [Code.stripCellXUpperCode,
    stripCellXUpperCost] using
    comp
      (natLt (IntEncoding.magnitude cell.1) period)
      (stripCellXUpperArguments width period cell)

def stripCellYUpperArgumentsCost
    (width period : Nat) (cell : Cell) : Nat :=
  prependCost
    [width, period, Encodable.encode cell]
    [IntEncoding.magnitude cell.2] [width]
    (stripCellFieldCost 2 width period cell)
    (getCost 0
      [width, period, Encodable.encode cell])

theorem stripCellYUpperArguments
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellYUpperArgumentsCode
      [width, period, Encodable.encode cell]
      [IntEncoding.magnitude cell.2, width]
      (stripCellYUpperArgumentsCost
        width period cell) := by
  simpa [Code.stripCellYUpperArgumentsCode,
    stripCellYUpperArgumentsCost, prependCost] using
    prepend
      (stripCellField 2 width period cell)
      (get 0
        [width, period, Encodable.encode cell])

def stripCellYUpperCost
    (width period : Nat) (cell : Cell) : Nat :=
  natLtCost (IntEncoding.magnitude cell.2) width +
    stripCellYUpperArgumentsCost width period cell

theorem stripCellYUpper
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellYUpperCode
      [width, period, Encodable.encode cell]
      [if IntEncoding.magnitude cell.2 < width
        then 1 else 0]
      (stripCellYUpperCost width period cell) := by
  simpa [Code.stripCellYUpperCode,
    stripCellYUpperCost] using
    comp
      (natLt (IntEncoding.magnitude cell.2) width)
      (stripCellYUpperArguments width period cell)

def stripCellYBothCost
    (width period : Nat) (cell : Cell) : Nat :=
  let yNonnegative :=
    if IntEncoding.sign cell.2 = 0 then 1 else 0
  let yUpper :=
    if IntEncoding.magnitude cell.2 < width then 1 else 0
  boolAndCost
    [width, period, Encodable.encode cell]
    yNonnegative yUpper
    (stripCellYNonnegativeCost width period cell)
    (stripCellYUpperCost width period cell)

theorem stripCellYBoth
    (width period : Nat) (cell : Cell) :
    let yNonnegative :=
      if IntEncoding.sign cell.2 = 0 then 1 else 0
    let yUpper :=
      if IntEncoding.magnitude cell.2 < width then 1 else 0
    EvaluatorCodeFits
      (Code.boolAnd Code.stripCellYNonnegativeCode
        Code.stripCellYUpperCode)
      [width, period, Encodable.encode cell]
      [if yNonnegative = 0 ∨ yUpper = 0 then 0 else 1]
      (stripCellYBothCost width period cell) := by
  simpa [stripCellYBothCost] using
    boolAnd
      (stripCellYNonnegative width period cell)
      (stripCellYUpper width period cell)

def stripCellXUpperAndYCost
    (width period : Nat) (cell : Cell) : Nat :=
  let xUpper :=
    if IntEncoding.magnitude cell.1 < period then 1 else 0
  let yNonnegative :=
    if IntEncoding.sign cell.2 = 0 then 1 else 0
  let yUpper :=
    if IntEncoding.magnitude cell.2 < width then 1 else 0
  let yBoth :=
    if yNonnegative = 0 ∨ yUpper = 0 then 0 else 1
  boolAndCost
    [width, period, Encodable.encode cell]
    xUpper yBoth
    (stripCellXUpperCost width period cell)
    (stripCellYBothCost width period cell)

theorem stripCellXUpperAndY
    (width period : Nat) (cell : Cell) :
    let xUpper :=
      if IntEncoding.magnitude cell.1 < period then 1 else 0
    let yNonnegative :=
      if IntEncoding.sign cell.2 = 0 then 1 else 0
    let yUpper :=
      if IntEncoding.magnitude cell.2 < width then 1 else 0
    let yBoth :=
      if yNonnegative = 0 ∨ yUpper = 0 then 0 else 1
    EvaluatorCodeFits
      (Code.boolAnd Code.stripCellXUpperCode <|
        Code.boolAnd Code.stripCellYNonnegativeCode
          Code.stripCellYUpperCode)
      [width, period, Encodable.encode cell]
      [if xUpper = 0 ∨ yBoth = 0 then 0 else 1]
      (stripCellXUpperAndYCost width period cell) := by
  simpa [stripCellXUpperAndYCost] using
    boolAnd
      (stripCellXUpper width period cell)
      (stripCellYBoth width period cell)

def stripCellInBoundsCost
    (width period : Nat) (cell : Cell) : Nat :=
  let xNonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let xUpper :=
    if IntEncoding.magnitude cell.1 < period then 1 else 0
  let yNonnegative :=
    if IntEncoding.sign cell.2 = 0 then 1 else 0
  let yUpper :=
    if IntEncoding.magnitude cell.2 < width then 1 else 0
  let yBoth :=
    if yNonnegative = 0 ∨ yUpper = 0 then 0 else 1
  let xUpperAndY :=
    if xUpper = 0 ∨ yBoth = 0 then 0 else 1
  boolAndCost
    [width, period, Encodable.encode cell]
    xNonnegative xUpperAndY
    (stripCellXNonnegativeCost width period cell)
    (stripCellXUpperAndYCost width period cell)

theorem stripCellInBounds
    (width period : Nat) (cell : Cell) :
    EvaluatorCodeFits Code.stripCellInBoundsCode
      [width, period, Encodable.encode cell]
      [if cell.InStripBounds width period then 1 else 0]
      (stripCellInBoundsCost width period cell) := by
  let xNonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let xUpper :=
    if IntEncoding.magnitude cell.1 < period then 1 else 0
  let yNonnegative :=
    if IntEncoding.sign cell.2 = 0 then 1 else 0
  let yUpper :=
    if IntEncoding.magnitude cell.2 < width then 1 else 0
  let yBoth :=
    if yNonnegative = 0 ∨ yUpper = 0 then 0 else 1
  let xUpperAndY :=
    if xUpper = 0 ∨ yBoth = 0 then 0 else 1
  have all :=
    boolAnd
      (stripCellXNonnegative width period cell)
      (stripCellXUpperAndY width period cell)
  by_cases xNonnegativeH :
      IntEncoding.sign cell.1 = 0 <;>
    by_cases xUpperH :
      IntEncoding.magnitude cell.1 < period <;>
    by_cases yNonnegativeH :
      IntEncoding.sign cell.2 = 0 <;>
    by_cases yUpperH :
      IntEncoding.magnitude cell.2 < width <;>
    simpa [Code.stripCellInBoundsCode,
      stripCellInBoundsCost, xNonnegative, xUpper,
      yNonnegative, yUpper, yBoth, xUpperAndY,
      Cell.inStripBounds_iff_encoding,
      xNonnegativeH, xUpperH,
      yNonnegativeH, yUpperH] using all

end EvaluatorCodeFits

end PartrecToTM2
end Turing

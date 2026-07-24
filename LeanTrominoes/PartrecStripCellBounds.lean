import LeanTrominoes.PartrecCellDecode
import LeanTrominoes.PartrecNatCompare
import LeanTrominoes.Periodic

/-!
# Explicit fundamental-domain test for one strip motif cell

Input is `[width, period, cellCode]`.  The cell decoder supplies magnitude
and sign fields; zero sign tags express nonnegativity, and natural strict
comparison checks the two upper bounds.
-/

namespace LeanTrominoes

def Cell.InStripBounds
    (width period : Nat) (cell : Cell) : Prop :=
  0 ≤ cell.1 ∧ cell.1 < (period : Int) ∧
    0 ≤ cell.2 ∧ cell.2 < (width : Int)

instance (width period : Nat) (cell : Cell) :
    Decidable (cell.InStripBounds width period) := by
  unfold Cell.InStripBounds
  infer_instance

theorem Cell.inStripBounds_iff_encoding
    (width period : Nat) (cell : Cell) :
    cell.InStripBounds width period ↔
      IntEncoding.sign cell.1 = 0 ∧
        IntEncoding.magnitude cell.1 < period ∧
        IntEncoding.sign cell.2 = 0 ∧
        IntEncoding.magnitude cell.2 < width := by
  rcases cell with ⟨x, y⟩
  cases x <;> cases y <;>
    simp [Cell.InStripBounds, IntEncoding.sign,
      IntEncoding.magnitude]

theorem PeriodicStrip.inFundamentalDomain_iff_bounds
    (periodicStrip : PeriodicStrip) (cell : Cell) :
    periodicStrip.InFundamentalDomain cell ↔
      cell.InStripBounds periodicStrip.width
        periodicStrip.period := by
  rfl

end LeanTrominoes

namespace Turing.ToPartrec.Code

open LeanTrominoes

/-- Decode the cell stored in field two of `[width, period, cellCode]`. -/
def stripCellViewCode : Code :=
  cellViewCode.comp (get 2)

/-- Select a fixed field of that decoded cell. -/
def stripCellFieldCode (field : Nat) : Code :=
  (get field).comp stripCellViewCode

@[simp]
theorem stripCellFieldCode_eval
    (field width period : Nat) (cell : Cell) :
    (stripCellFieldCode field).eval
        [width, period, Encodable.encode cell] =
      pure
        [[IntEncoding.magnitude cell.1,
            IntEncoding.sign cell.1,
            IntEncoding.magnitude cell.2,
            IntEncoding.sign cell.2][field]?.getD 0] := by
  simp [stripCellFieldCode, stripCellViewCode]

def stripCellXNonnegativeCode : Code :=
  isZero (stripCellFieldCode 1)

@[simp]
theorem stripCellXNonnegativeCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellXNonnegativeCode.eval
        [width, period, Encodable.encode cell] =
      pure
        [if IntEncoding.sign cell.1 = 0 then 1 else 0] := by
  exact
    isZero_eval_at (stripCellFieldCode 1)
      [width, period, Encodable.encode cell]
      (IntEncoding.sign cell.1) (by simp)

def stripCellYNonnegativeCode : Code :=
  isZero (stripCellFieldCode 3)

@[simp]
theorem stripCellYNonnegativeCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellYNonnegativeCode.eval
        [width, period, Encodable.encode cell] =
      pure
        [if IntEncoding.sign cell.2 = 0 then 1 else 0] := by
  exact
    isZero_eval_at (stripCellFieldCode 3)
      [width, period, Encodable.encode cell]
      (IntEncoding.sign cell.2) (by simp)

def stripCellXUpperArgumentsCode : Code :=
  prepend (stripCellFieldCode 0) (get 1)

@[simp]
theorem stripCellXUpperArgumentsCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellXUpperArgumentsCode.eval
        [width, period, Encodable.encode cell] =
      pure [IntEncoding.magnitude cell.1, period] := by
  simp [stripCellXUpperArgumentsCode]

def stripCellXUpperCode : Code :=
  natLtCode.comp stripCellXUpperArgumentsCode

@[simp]
theorem stripCellXUpperCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellXUpperCode.eval
        [width, period, Encodable.encode cell] =
      pure
        [if IntEncoding.magnitude cell.1 < period
          then 1 else 0] := by
  simp [stripCellXUpperCode]

def stripCellYUpperArgumentsCode : Code :=
  prepend (stripCellFieldCode 2) (get 0)

@[simp]
theorem stripCellYUpperArgumentsCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellYUpperArgumentsCode.eval
        [width, period, Encodable.encode cell] =
      pure [IntEncoding.magnitude cell.2, width] := by
  simp [stripCellYUpperArgumentsCode]

def stripCellYUpperCode : Code :=
  natLtCode.comp stripCellYUpperArgumentsCode

@[simp]
theorem stripCellYUpperCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellYUpperCode.eval
        [width, period, Encodable.encode cell] =
      pure
        [if IntEncoding.magnitude cell.2 < width
          then 1 else 0] := by
  simp [stripCellYUpperCode]

/-- Return one exactly when the encoded cell lies in the selected strip
fundamental domain. -/
def stripCellInBoundsCode : Code :=
  boolAnd stripCellXNonnegativeCode <|
    boolAnd stripCellXUpperCode <|
      boolAnd stripCellYNonnegativeCode
        stripCellYUpperCode

@[simp]
theorem stripCellInBoundsCode_eval
    (width period : Nat) (cell : Cell) :
    stripCellInBoundsCode.eval
        [width, period, Encodable.encode cell] =
      pure [if cell.InStripBounds width period then 1 else 0] := by
  let values :=
    [width, period, Encodable.encode cell]
  let xNonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let xUpper :=
    if IntEncoding.magnitude cell.1 < period then 1 else 0
  let yNonnegative :=
    if IntEncoding.sign cell.2 = 0 then 1 else 0
  let yUpper :=
    if IntEncoding.magnitude cell.2 < width then 1 else 0
  have yBoth :=
    boolAnd_eval_at stripCellYNonnegativeCode
      stripCellYUpperCode values yNonnegative yUpper
      (by simp [values, yNonnegative])
      (by simp [values, yUpper])
  let yBothValue :=
    if yNonnegative = 0 ∨ yUpper = 0 then 0 else 1
  have xUpperAndY :=
    boolAnd_eval_at stripCellXUpperCode
      (boolAnd stripCellYNonnegativeCode
        stripCellYUpperCode)
      values xUpper yBothValue
      (by simp [values, xUpper]) yBoth
  let xUpperAndYValue :=
    if xUpper = 0 ∨ yBothValue = 0 then 0 else 1
  have all :=
    boolAnd_eval_at stripCellXNonnegativeCode
      (boolAnd stripCellXUpperCode <|
        boolAnd stripCellYNonnegativeCode
          stripCellYUpperCode)
      values xNonnegative xUpperAndYValue
      (by simp [values, xNonnegative])
      xUpperAndY
  simp only [stripCellInBoundsCode]
  by_cases xNonnegativeH :
      IntEncoding.sign cell.1 = 0 <;>
    by_cases xUpperH :
      IntEncoding.magnitude cell.1 < period <;>
    by_cases yNonnegativeH :
      IntEncoding.sign cell.2 = 0 <;>
    by_cases yUpperH :
      IntEncoding.magnitude cell.2 < width <;>
    simpa [values, xNonnegative, xUpper,
      yNonnegative, yUpper, yBothValue,
      xUpperAndYValue,
      Cell.inStripBounds_iff_encoding,
      xNonnegativeH, xUpperH,
      yNonnegativeH, yUpperH] using all

end Turing.ToPartrec.Code

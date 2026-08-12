import LeanTrominoes.PartrecIntOffset
import LeanTrominoes.PartrecPackedColumnPhase
import LeanTrominoes.PartrecPair

/-!
# Canonical target cells for packed frontier checks

Center validity repeatedly asks about a cell obtained from one of the five
frontier columns and a fixed vertical displacement.  On native input
`[period, phase, column, encodedRow]`, this file computes the represented
column phase, encodes that nonnegative integer as an `Int`, offsets the row,
and pairs the two standard integer encodings into the standard `Cell` code.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

/-- Select `[period, phase, column]` from the four-field target input. -/
def packedTargetColumnArgumentsCode : Code :=
  prepend (get 0) <| prepend (get 1) (get 2)

@[simp]
theorem packedTargetColumnArgumentsCode_eval
    (period phase column rowCode : Nat) :
    packedTargetColumnArgumentsCode.eval
        [period, phase, column, rowCode] =
      pure [period, phase, column] := by
  simp [packedTargetColumnArgumentsCode]

/-- Compute the canonical nonnegative coordinate of the queried column. -/
def packedTargetColumnPhaseCode : Code :=
  packedColumnPhaseCode.comp packedTargetColumnArgumentsCode

@[simp]
theorem packedTargetColumnPhaseCode_eval
    (period phase column rowCode : Nat) :
    packedTargetColumnPhaseCode.eval
        [period, phase, column, rowCode] =
      pure [packedColumnPhaseNumerator period phase column % period] := by
  simp [packedTargetColumnPhaseCode]

/-- Duplicate the natural column phase so addition encodes it as a
nonnegative integer (`encode (Int.ofNat x) = x + x`). -/
def packedTargetXArgumentsCode : Code :=
  prepend packedTargetColumnPhaseCode packedTargetColumnPhaseCode

@[simp]
theorem packedTargetXArgumentsCode_eval
    (period phase column rowCode : Nat) :
    packedTargetXArgumentsCode.eval
        [period, phase, column, rowCode] =
      let x := packedColumnPhaseNumerator period phase column % period
      pure [x, x] := by
  simp [packedTargetXArgumentsCode]

/-- Standard integer encoding of the canonical nonnegative column phase. -/
def packedTargetXCode : Code :=
  natAddCode.comp packedTargetXArgumentsCode

@[simp]
theorem packedTargetXCode_eval
    (period phase column rowCode : Nat) :
    packedTargetXCode.eval [period, phase, column, rowCode] =
      let x := packedColumnPhaseNumerator period phase column % period
      pure [2 * x] := by
  simp [packedTargetXCode]
  omega

/-- Apply a fixed vertical displacement to the encoded row field. -/
def packedTargetYCode (verticalOffset : Int) : Code :=
  (intOffsetCode verticalOffset).comp (get 3)

@[simp]
theorem packedTargetYCode_eval
    (verticalOffset : Int) (period phase column : Nat) (row : Int) :
    (packedTargetYCode verticalOffset).eval
        [period, phase, column, Encodable.encode row] =
      pure [Encodable.encode (row + verticalOffset)] := by
  simp [packedTargetYCode]

/-- Assemble the two standard integer encodings of the target cell. -/
def packedTargetCellArgumentsCode (verticalOffset : Int) : Code :=
  prepend packedTargetXCode (packedTargetYCode verticalOffset)

@[simp]
theorem packedTargetCellArgumentsCode_eval
    (verticalOffset : Int) (period phase column : Nat) (row : Int) :
    (packedTargetCellArgumentsCode verticalOffset).eval
        [period, phase, column, Encodable.encode row] =
      let x := packedColumnPhaseNumerator period phase column % period
      pure [2 * x,
        Encodable.encode (row + verticalOffset)] := by
  simp [packedTargetCellArgumentsCode,
    packedTargetXCode_eval]

/-- Encode the canonical target cell represented by one frontier column and
a fixed vertical displacement from the input row. -/
def packedTargetCellCode (verticalOffset : Int) : Code :=
  natPairCode.comp (packedTargetCellArgumentsCode verticalOffset)

@[simp]
theorem packedTargetCellCode_eval
    (verticalOffset : Int) (period phase column : Nat) (row : Int) :
    (packedTargetCellCode verticalOffset).eval
        [period, phase, column, Encodable.encode row] =
      let x := packedColumnPhaseNumerator period phase column % period
      pure [Encodable.encode
        ((Int.ofNat x, row + verticalOffset) : Cell)] := by
  let x := packedColumnPhaseNumerator period phase column % period
  have arguments := packedTargetCellArgumentsCode_eval
    verticalOffset period phase column row
  calc
    _ = natPairCode.eval
        [2 * x, Encodable.encode (row + verticalOffset)] := by
      simp [packedTargetCellCode, arguments, x]
    _ = pure
        [Nat.pair (2 * x)
          (Encodable.encode (row + verticalOffset))] := by
      rw [natPairCode_eval]
    _ = pure [Encodable.encode
        ((Int.ofNat x, row + verticalOffset) : Cell)] := by
      simp only [Encodable.encode_prod_val,
        IntEncoding.encode_ofNat]

@[simp]
theorem packedTargetCellCode_eval_semantic
    (verticalOffset : Int) (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn)
    (row : Int) :
    (packedTargetCellCode verticalOffset).eval
        [periodicStrip.period, packed.phase, column.val,
          Encodable.encode row] =
      pure [Encodable.encode
        ((((packed.columnPhase periodicStrip column : Nat) : Int),
          row + verticalOffset) : Cell)] := by
  rw [packedTargetCellCode_eval]
  simp [PackedWindowState.columnPhase,
    packedColumnPhaseNumerator, packedColumnPhaseSum]
  congr 4
  omega

end Turing.ToPartrec.Code

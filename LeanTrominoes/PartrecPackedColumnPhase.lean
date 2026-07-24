import LeanTrominoes.PartrecAdd
import LeanTrominoes.PartrecDivision
import LeanTrominoes.StripFrontierPacked

/-!
# Packed frontier column-phase arithmetic

For native input `[period, phase, column]`, this module computes

`(phase + column + 2 * period - 2) % period`,

the horizontal coordinate represented by one of the five frontier columns.
All intermediate results remain fixed-width native natural lists.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

def packedColumnPhaseSum
    (period phase column : Nat) : Nat :=
  phase + column + (period + period)

def packedColumnPhaseNumerator
    (period phase column : Nat) : Nat :=
  packedColumnPhaseSum period phase column - 2

/-- Assemble `[period, period]`. -/
def packedColumnPhaseDoublePeriodArgumentsCode : Code :=
  prepend (get 0) (get 0)

def packedColumnPhaseDoublePeriodCode : Code :=
  natAddCode.comp packedColumnPhaseDoublePeriodArgumentsCode

@[simp]
theorem packedColumnPhaseDoublePeriodCode_eval
    (period phase column : Nat) :
    packedColumnPhaseDoublePeriodCode.eval
        [period, phase, column] =
      pure [period + period] := by
  simp [packedColumnPhaseDoublePeriodCode,
    packedColumnPhaseDoublePeriodArgumentsCode]

/-- Assemble `[phase, column]`. -/
def packedColumnPhaseOffsetArgumentsCode : Code :=
  prepend (get 1) (get 2)

def packedColumnPhaseOffsetCode : Code :=
  natAddCode.comp packedColumnPhaseOffsetArgumentsCode

@[simp]
theorem packedColumnPhaseOffsetCode_eval
    (period phase column : Nat) :
    packedColumnPhaseOffsetCode.eval
        [period, phase, column] =
      pure [phase + column] := by
  simp [packedColumnPhaseOffsetCode,
    packedColumnPhaseOffsetArgumentsCode]

/-- Assemble `[phase + column, 2 * period]`. -/
def packedColumnPhaseSumArgumentsCode : Code :=
  prepend packedColumnPhaseOffsetCode
    packedColumnPhaseDoublePeriodCode

def packedColumnPhaseSumCode : Code :=
  natAddCode.comp packedColumnPhaseSumArgumentsCode

@[simp]
theorem packedColumnPhaseSumCode_eval
    (period phase column : Nat) :
    packedColumnPhaseSumCode.eval
        [period, phase, column] =
      pure [packedColumnPhaseSum period phase column] := by
  simp [packedColumnPhaseSumCode,
    packedColumnPhaseSumArgumentsCode,
    packedColumnPhaseSum]

/-- Subtract the fixed two-column center offset. -/
def packedColumnPhaseNumeratorCode : Code :=
  pred.comp (pred.comp packedColumnPhaseSumCode)

@[simp]
theorem packedColumnPhaseNumeratorCode_eval
    (period phase column : Nat) :
    packedColumnPhaseNumeratorCode.eval
        [period, phase, column] =
      pure [packedColumnPhaseNumerator period phase column] := by
  simp [packedColumnPhaseNumeratorCode,
    packedColumnPhaseNumerator]
  omega

/-- Assemble `[numerator, period]` for quotient/remainder division. -/
def packedColumnPhaseDivisionArgumentsCode : Code :=
  prepend packedColumnPhaseNumeratorCode (get 0)

def packedColumnPhaseDivisionCode : Code :=
  divisionCode.comp packedColumnPhaseDivisionArgumentsCode

@[simp]
theorem packedColumnPhaseDivisionCode_eval
    (period phase column : Nat) :
    packedColumnPhaseDivisionCode.eval
        [period, phase, column] =
      pure
        [packedColumnPhaseNumerator period phase column / period,
          packedColumnPhaseNumerator period phase column % period] := by
  simp [packedColumnPhaseDivisionCode,
    packedColumnPhaseDivisionArgumentsCode]

/-- Return just the wrapped column phase. -/
def packedColumnPhaseCode : Code :=
  (get 1).comp packedColumnPhaseDivisionCode

@[simp]
theorem packedColumnPhaseCode_eval
    (period phase column : Nat) :
    packedColumnPhaseCode.eval [period, phase, column] =
      pure
        [packedColumnPhaseNumerator period phase column % period] := by
  simp [packedColumnPhaseCode]

theorem packedColumnPhaseCode_eval_semantic
    (periodicStrip : PeriodicStrip)
    (packed : PeriodicStrip.PackedWindowState)
    (column : PeriodicStrip.WindowColumn) :
    packedColumnPhaseCode.eval
        [periodicStrip.period, packed.phase, column.val] =
      pure [packed.columnPhase periodicStrip column] := by
  simp [PeriodicStrip.PackedWindowState.columnPhase,
    packedColumnPhaseNumerator, packedColumnPhaseSum]
  congr 2
  omega

end Turing.ToPartrec.Code

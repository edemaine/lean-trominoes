import LeanTrominoes.PartrecPackedNormalizationAll
import LeanTrominoes.PartrecPackedNormalizationLoopSpace

/-!
# Evaluator-space composition for complete frontier normalization

This file composes the five fitted streaming column calls through the fixed
Boolean conjunction used by `packedNormalizationAllCode`.  The exact cost
terms remain continuation-independent and are ready for a common polynomial
majorant in the strip transition budget.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private theorem boolAnd_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolAnd leftCode rightCode) values
      [(left && right).toNat]
      (boolAndCost values left.toNat right.toNat leftCost rightCost) := by
  have combined := boolAnd leftFit rightFit
  cases left <;> cases right <;> simpa using combined

def packedNormalizationColumnArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  let restWord := getCost 3 values
  let restColumn :=
    prependCost values [column.val]
      [packed.assignmentWord]
      (numeralCost column.val values) restWord
  let restMotif :=
    prependCost values [Encodable.encode periodicStrip.motif]
      [column.val, packed.assignmentWord]
      (getCost 2 values) restColumn
  let restPhase :=
    prependCost values [packed.phase]
      [Encodable.encode periodicStrip.motif,
        column.val, packed.assignmentWord]
      (getCost 1 values) restMotif
  prependCost values [periodicStrip.period]
    [packed.phase, Encodable.encode periodicStrip.motif,
      column.val, packed.assignmentWord]
    (getCost 0 values) restPhase

theorem packedNormalizationColumnArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    EvaluatorCodeFits
      (Code.packedNormalizationColumnArgumentsCode column)
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        column.val, packed.assignmentWord]
      (packedNormalizationColumnArgumentsCost
        periodicStrip packed column) := by
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  have restWord := get 3 values
  have restColumn := prepend (numeral column.val values) restWord
  have restMotif := prepend (get 2 values) restColumn
  have restPhase := prepend (get 1 values) restMotif
  have result := prepend (get 0 values) restPhase
  simpa [Code.packedNormalizationColumnArgumentsCode,
    packedNormalizationColumnArgumentsCost,
    Code.numeral, numeralCost, prependCost, values] using result

def packedNormalizationColumnAtCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) : Nat :=
  packedNormalizationColumnCost periodicStrip packed column +
    packedNormalizationColumnArgumentsCost
      periodicStrip packed column

theorem packedNormalizationColumnAt
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    EvaluatorCodeFits
      (Code.packedNormalizationColumnAtCode column)
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [(packed.normalizedColumnBool periodicStrip column).toNat]
      (packedNormalizationColumnAtCost
        periodicStrip packed column) := by
  simpa [Code.packedNormalizationColumnAtCode,
    packedNormalizationColumnAtCost] using
    comp
      (packedNormalizationColumn periodicStrip packed column)
      (packedNormalizationColumnArguments periodicStrip packed column)

def packedNormalizationLastTwoCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  boolAndCost values
    (packed.normalizedColumnBool periodicStrip
      (3 : WindowColumn)).toNat
    (packed.normalizedColumnBool periodicStrip
      (4 : WindowColumn)).toNat
    (packedNormalizationColumnAtCost
      periodicStrip packed (3 : WindowColumn))
    (packedNormalizationColumnAtCost
      periodicStrip packed (4 : WindowColumn))

theorem packedNormalizationLastTwo
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.packedNormalizationColumnAtCode (3 : WindowColumn))
        (Code.packedNormalizationColumnAtCode (4 : WindowColumn)))
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [(packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        packed.normalizedColumnBool periodicStrip
          (4 : WindowColumn)).toNat]
      (packedNormalizationLastTwoCost periodicStrip packed) := by
  simpa [packedNormalizationLastTwoCost] using boolAnd_fit_bool
    (packed.normalizedColumnBool periodicStrip (3 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (4 : WindowColumn))
    (packedNormalizationColumnAt
      periodicStrip packed (3 : WindowColumn))
    (packedNormalizationColumnAt
      periodicStrip packed (4 : WindowColumn))

def packedNormalizationLastThreeCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  boolAndCost values
    (packed.normalizedColumnBool periodicStrip
      (2 : WindowColumn)).toNat
    (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
      packed.normalizedColumnBool periodicStrip
        (4 : WindowColumn)).toNat
    (packedNormalizationColumnAtCost
      periodicStrip packed (2 : WindowColumn))
    (packedNormalizationLastTwoCost periodicStrip packed)

theorem packedNormalizationLastThree
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.packedNormalizationColumnAtCode (2 : WindowColumn))
        (Code.boolAnd
          (Code.packedNormalizationColumnAtCode (3 : WindowColumn))
          (Code.packedNormalizationColumnAtCode (4 : WindowColumn))))
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [(packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          packed.normalizedColumnBool periodicStrip
            (4 : WindowColumn))).toNat]
      (packedNormalizationLastThreeCost periodicStrip packed) := by
  simpa [packedNormalizationLastThreeCost] using boolAnd_fit_bool
    (packed.normalizedColumnBool periodicStrip (2 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
      packed.normalizedColumnBool periodicStrip (4 : WindowColumn))
    (packedNormalizationColumnAt
      periodicStrip packed (2 : WindowColumn))
    (packedNormalizationLastTwo periodicStrip packed)

def packedNormalizationLastFourCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  boolAndCost values
    (packed.normalizedColumnBool periodicStrip
      (1 : WindowColumn)).toNat
    (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
      (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        packed.normalizedColumnBool periodicStrip
          (4 : WindowColumn))).toNat
    (packedNormalizationColumnAtCost
      periodicStrip packed (1 : WindowColumn))
    (packedNormalizationLastThreeCost periodicStrip packed)

theorem packedNormalizationLastFour
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.packedNormalizationColumnAtCode (1 : WindowColumn))
        (Code.boolAnd
          (Code.packedNormalizationColumnAtCode (2 : WindowColumn))
          (Code.boolAnd
            (Code.packedNormalizationColumnAtCode (3 : WindowColumn))
            (Code.packedNormalizationColumnAtCode (4 : WindowColumn)))))
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [(packed.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
          (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
            packed.normalizedColumnBool periodicStrip
              (4 : WindowColumn)))).toNat]
      (packedNormalizationLastFourCost periodicStrip packed) := by
  simpa [packedNormalizationLastFourCost] using boolAnd_fit_bool
    (packed.normalizedColumnBool periodicStrip (1 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
      (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        packed.normalizedColumnBool periodicStrip (4 : WindowColumn)))
    (packedNormalizationColumnAt
      periodicStrip packed (1 : WindowColumn))
    (packedNormalizationLastThree periodicStrip packed)

def packedNormalizationAllCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  boolAndCost values
    (packed.normalizedColumnBool periodicStrip
      (0 : WindowColumn)).toNat
    (packed.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
      (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          packed.normalizedColumnBool periodicStrip
            (4 : WindowColumn)))).toNat
    (packedNormalizationColumnAtCost
      periodicStrip packed (0 : WindowColumn))
    (packedNormalizationLastFourCost periodicStrip packed)

/-- Exact fitted certificate for the complete normalization program. -/
theorem packedNormalizationAll
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    EvaluatorCodeFits Code.packedNormalizationAllCode
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [(packed.isNormalizedBool periodicStrip).toNat]
      (packedNormalizationAllCost periodicStrip packed) := by
  have combined := boolAnd_fit_bool
    (packed.normalizedColumnBool periodicStrip (0 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
      (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          packed.normalizedColumnBool periodicStrip (4 : WindowColumn))))
    (packedNormalizationColumnAt
      periodicStrip packed (0 : WindowColumn))
    (packedNormalizationLastFour periodicStrip packed)
  have columns :
      (List.finRange 5 : List (Fin 5)) = [0, 1, 2, 3, 4] := by
    native_decide
  rw [PackedWindowState.isNormalizedBool, columns]
  simpa [Code.packedNormalizationAllCode,
    packedNormalizationAllCost] using combined

end EvaluatorCodeFits

end PartrecToTM2
end Turing

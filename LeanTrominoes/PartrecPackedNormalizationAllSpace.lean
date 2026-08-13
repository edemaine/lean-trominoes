/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- One arithmetic envelope shared by all five fixed normalization-column
calls.  The repeated motif terms absorb the encoded suffixes retained by the
streaming implementation, while the fixed column indices fit in the slack. -/
def packedNormalizationAllLimit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  4096 * (periodicStrip.period + packed.phase +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    Encodable.encode periodicStrip.motif +
    packed.assignmentWord + 200) + 3000

/-- Uniform workspace unit for the complete five-column normalizer. -/
def packedNormalizationAllUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  encodedListSpace
    [packedNormalizationAllLimit periodicStrip packed] + 1

private theorem packedNormalizationColumnUnit_le_allUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    encodedListSpace
          [4096 * (periodicStrip.period + packed.phase +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            Encodable.encode periodicStrip.motif +
            column.val + packed.assignmentWord + 100) + 2000] + 1 ≤
      packedNormalizationAllUnit periodicStrip packed := by
  let small :=
    4096 * (periodicStrip.period + packed.phase +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      Encodable.encode periodicStrip.motif +
      column.val + packed.assignmentWord + 100) + 2000
  let large := packedNormalizationAllLimit periodicStrip packed
  have valueBound : small ≤ large := by
    simp only [small, large, packedNormalizationAllLimit]
    have columnLt : column.val < 5 := column.isLt
    omega
  have bitsBound := encodeNat_length_mono valueBound
  simpa [small, large, packedNormalizationAllUnit,
    encodedListSpace_cons, encodedListSpace_nil] using bitsBound

private theorem packedNormalizationColumnCost_le_allUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationColumnCost periodicStrip packed column ≤
      2000000000000000000000000000000000 *
        packedNormalizationAllUnit periodicStrip packed := by
  exact (packedNormalizationColumnCost_le_linear
    periodicStrip packed column).trans
      (Nat.mul_le_mul_left _
        (packedNormalizationColumnUnit_le_allUnit
          periodicStrip packed column))

set_option maxHeartbeats 800000 in
private theorem packedNormalizationColumnArgumentsCost_le_allUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationColumnArgumentsCost periodicStrip packed column ≤
      1000000000 *
        packedNormalizationAllUnit periodicStrip packed := by
  let limit := packedNormalizationAllLimit periodicStrip packed
  let unit := packedNormalizationAllUnit periodicStrip packed
  have periodBound : periodicStrip.period ≤ limit := by
    simp only [limit, packedNormalizationAllLimit]
    omega
  have phaseBound : packed.phase ≤ limit := by
    simp only [limit, packedNormalizationAllLimit]
    omega
  have motifBound : Encodable.encode periodicStrip.motif ≤ limit := by
    simp only [limit, packedNormalizationAllLimit]
    omega
  have columnBound : column.val ≤ limit := by
    simp only [limit, packedNormalizationAllLimit]
    omega
  have wordBound : packed.assignmentWord ≤ limit := by
    simp only [limit, packedNormalizationAllLimit]
    omega
  have periodBits := encodeNat_length_mono periodBound
  have phaseBits := encodeNat_length_mono phaseBound
  have motifBits := encodeNat_length_mono motifBound
  have columnBits := encodeNat_length_mono columnBound
  have wordBits := encodeNat_length_mono wordBound
  have periodSuccBits := encodeNat_length_mono
    (show periodicStrip.period + 1 ≤ limit by
      simp only [limit, packedNormalizationAllLimit]
      omega)
  have phaseSuccBits := encodeNat_length_mono
    (show packed.phase + 1 ≤ limit by
      simp only [limit, packedNormalizationAllLimit]
      omega)
  have motifSuccBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip.motif + 1 ≤ limit by
      simp only [limit, packedNormalizationAllLimit]
      omega)
  have wordSuccBits := encodeNat_length_mono
    (show packed.assignmentWord + 1 ≤ limit by
      simp only [limit, packedNormalizationAllLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    dsimp only [unit, limit]
    simp [packedNormalizationAllUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have numeralColumnCost :
      addConstCost column.val [0] ≤ 1000000 * unit := by
    have raw := addConstCost_le column.val [0]
    have columnLt : column.val < 5 := column.isLt
    have unitPositive : 1 ≤ unit := by
      simp [unit, packedNormalizationAllUnit]
    have zeroBits :
        (Computability.encodeNat 0).length = 0 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil,
      zeroBits] at raw
    nlinarith
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [packedNormalizationColumnArgumentsCost,
    prependCost, numeralCost,
    getCost, dropCost, headCost, idCost,
    nilCost, zeroCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits]
  clear * - periodBits phaseBits motifBits columnBits wordBits
    periodSuccBits phaseSuccBits motifSuccBits wordSuccBits
    numeralColumnCost unitEq
  omega

private theorem packedNormalizationColumnAtCost_le_allUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    packedNormalizationColumnAtCost periodicStrip packed column ≤
      3000000000000000000000000000000000 *
        packedNormalizationAllUnit periodicStrip packed := by
  have columnCost := packedNormalizationColumnCost_le_allUnit
    periodicStrip packed column
  have argumentsCost :=
    packedNormalizationColumnArgumentsCost_le_allUnit
      periodicStrip packed column
  simp only [packedNormalizationColumnAtCost]
  omega

set_option maxHeartbeats 2500000 in
/-- The complete fixed five-column normalization conjunction has one
input-linear evaluator-space majorant. -/
theorem packedNormalizationAllCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedNormalizationAllCost periodicStrip packed ≤
      10000000000000000000000000000000000000000000000000000 *
        packedNormalizationAllUnit periodicStrip packed := by
  let unit := packedNormalizationAllUnit periodicStrip packed
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  let baseBudget :=
    3000000000000000000000000000000000 * unit
  let secondBudget := 1000 * (baseBudget + 1)
  let thirdBudget := 1000 * (secondBudget + 1)
  let fourthBudget := 1000 * (thirdBudget + 1)
  let finalBudget := 1000 * (fourthBudget + 1)
  have unitPositive : 1 ≤ unit := by
    simp [unit, packedNormalizationAllUnit]
  have unitEq :
      unit =
        (Computability.encodeNat
          (packedNormalizationAllLimit periodicStrip packed)).length + 2 := by
    simp [unit, packedNormalizationAllUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have valuesSpace : encodedListSpace values ≤ 10 * unit := by
    have periodBound :
        periodicStrip.period ≤
          packedNormalizationAllLimit periodicStrip packed := by
      simp only [packedNormalizationAllLimit]
      omega
    have phaseBound :
        packed.phase ≤
          packedNormalizationAllLimit periodicStrip packed := by
      simp only [packedNormalizationAllLimit]
      omega
    have motifBound :
        Encodable.encode periodicStrip.motif ≤
          packedNormalizationAllLimit periodicStrip packed := by
      simp only [packedNormalizationAllLimit]
      omega
    have wordBound :
        packed.assignmentWord ≤
          packedNormalizationAllLimit periodicStrip packed := by
      simp only [packedNormalizationAllLimit]
      omega
    have periodBits := encodeNat_length_mono periodBound
    have phaseBits := encodeNat_length_mono phaseBound
    have motifBits := encodeNat_length_mono motifBound
    have wordBits := encodeNat_length_mono wordBound
    simp only [values, encodedListSpace_cons, encodedListSpace_nil]
    rw [unitEq]
    omega
  have headBits :
      (Computability.encodeNat values.headI).length ≤ 10 * unit := by
    simp [values] at valuesSpace ⊢
    omega
  have headSuccBits :
      (Computability.encodeNat (values.headI + 1)).length ≤
        20 * unit := by
    have successor := encodeNat_succ_length_le values.headI
    have successor' :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using successor
    omega
  have cost0 := packedNormalizationColumnAtCost_le_allUnit
    periodicStrip packed (0 : WindowColumn)
  have cost1 := packedNormalizationColumnAtCost_le_allUnit
    periodicStrip packed (1 : WindowColumn)
  have cost2 := packedNormalizationColumnAtCost_le_allUnit
    periodicStrip packed (2 : WindowColumn)
  have cost3 := packedNormalizationColumnAtCost_le_allUnit
    periodicStrip packed (3 : WindowColumn)
  have cost4 := packedNormalizationColumnAtCost_le_allUnit
    periodicStrip packed (4 : WindowColumn)
  have valuesBase : encodedListSpace values ≤ baseBudget := by
    simp only [baseBudget]
    omega
  have headBase :
      (Computability.encodeNat values.headI).length ≤ baseBudget := by
    simp only [baseBudget]
    omega
  have headSuccBase :
      (Computability.encodeNat (values.headI + 1)).length ≤
        baseBudget := by
    simp only [baseBudget]
    omega
  have cost0Base :
      packedNormalizationColumnAtCost
          periodicStrip packed (0 : WindowColumn) ≤ baseBudget := by
    simpa [baseBudget, unit] using cost0
  have cost1Base :
      packedNormalizationColumnAtCost
          periodicStrip packed (1 : WindowColumn) ≤ baseBudget := by
    simpa [baseBudget, unit] using cost1
  have cost2Base :
      packedNormalizationColumnAtCost
          periodicStrip packed (2 : WindowColumn) ≤ baseBudget := by
    simpa [baseBudget, unit] using cost2
  have cost3Base :
      packedNormalizationColumnAtCost
          periodicStrip packed (3 : WindowColumn) ≤ baseBudget := by
    simpa [baseBudget, unit] using cost3
  have cost4Base :
      packedNormalizationColumnAtCost
          periodicStrip packed (4 : WindowColumn) ≤ baseBudget := by
    simpa [baseBudget, unit] using cost4
  have tag0 :
      (packed.normalizedColumnBool
        periodicStrip (0 : WindowColumn)).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (0 : WindowColumn) <;>
      simp
  have tag1 :
      (packed.normalizedColumnBool
        periodicStrip (1 : WindowColumn)).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (1 : WindowColumn) <;>
      simp
  have tag2 :
      (packed.normalizedColumnBool
        periodicStrip (2 : WindowColumn)).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (2 : WindowColumn) <;>
      simp
  have tag3 :
      (packed.normalizedColumnBool
        periodicStrip (3 : WindowColumn)).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (3 : WindowColumn) <;>
      simp
  have tag4 :
      (packed.normalizedColumnBool
        periodicStrip (4 : WindowColumn)).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (4 : WindowColumn) <;>
      simp
  have lastTwoBound :
      packedNormalizationLastTwoCost periodicStrip packed ≤
        secondBudget := by
    have bound := boolAndCost_le_budget values
      (packed.normalizedColumnBool
        periodicStrip (3 : WindowColumn)).toNat
      (packed.normalizedColumnBool
        periodicStrip (4 : WindowColumn)).toNat
      (packedNormalizationColumnAtCost
        periodicStrip packed (3 : WindowColumn))
      (packedNormalizationColumnAtCost
        periodicStrip packed (4 : WindowColumn))
      baseBudget tag3 tag4 valuesBase headBase headSuccBase
      cost3Base cost4Base (by
        simp only [baseBudget]
        exact Nat.mul_pos (by norm_num) (by omega))
    simpa [packedNormalizationLastTwoCost, values,
      secondBudget] using bound
  have valuesSecond : encodedListSpace values ≤ secondBudget :=
    valuesBase.trans (by simp only [secondBudget]; omega)
  have headSecond :
      (Computability.encodeNat values.headI).length ≤ secondBudget :=
    headBase.trans (by simp only [secondBudget]; omega)
  have headSuccSecond :
      (Computability.encodeNat (values.headI + 1)).length ≤
        secondBudget :=
    headSuccBase.trans (by simp only [secondBudget]; omega)
  have cost2Second :
      packedNormalizationColumnAtCost
          periodicStrip packed (2 : WindowColumn) ≤ secondBudget :=
    cost2Base.trans (by simp only [secondBudget]; omega)
  have tagLastTwo :
      (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        packed.normalizedColumnBool
          periodicStrip (4 : WindowColumn)).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (3 : WindowColumn) <;>
      cases packed.normalizedColumnBool
        periodicStrip (4 : WindowColumn) <;> simp
  have lastThreeBound :
      packedNormalizationLastThreeCost periodicStrip packed ≤
        thirdBudget := by
    have bound := boolAndCost_le_budget values
      (packed.normalizedColumnBool
        periodicStrip (2 : WindowColumn)).toNat
      (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        packed.normalizedColumnBool
          periodicStrip (4 : WindowColumn)).toNat
      (packedNormalizationColumnAtCost
        periodicStrip packed (2 : WindowColumn))
      (packedNormalizationLastTwoCost periodicStrip packed)
      secondBudget tag2 tagLastTwo valuesSecond headSecond
      headSuccSecond cost2Second lastTwoBound (by
        simp only [secondBudget]
        exact Nat.mul_pos (by norm_num) (Nat.succ_pos _))
    simpa [packedNormalizationLastThreeCost, values,
      thirdBudget] using bound
  have valuesThird : encodedListSpace values ≤ thirdBudget :=
    valuesSecond.trans (by simp only [thirdBudget]; omega)
  have headThird :
      (Computability.encodeNat values.headI).length ≤ thirdBudget :=
    headSecond.trans (by simp only [thirdBudget]; omega)
  have headSuccThird :
      (Computability.encodeNat (values.headI + 1)).length ≤
        thirdBudget :=
    headSuccSecond.trans (by simp only [thirdBudget]; omega)
  have cost1Third :
      packedNormalizationColumnAtCost
          periodicStrip packed (1 : WindowColumn) ≤ thirdBudget :=
    cost1Base.trans (by
      simp only [thirdBudget, secondBudget]
      omega)
  have tagLastThree :
      (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          packed.normalizedColumnBool
            periodicStrip (4 : WindowColumn))).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (2 : WindowColumn) <;>
      cases packed.normalizedColumnBool
        periodicStrip (3 : WindowColumn) <;>
      cases packed.normalizedColumnBool
        periodicStrip (4 : WindowColumn) <;> simp
  have lastFourBound :
      packedNormalizationLastFourCost periodicStrip packed ≤
        fourthBudget := by
    have bound := boolAndCost_le_budget values
      (packed.normalizedColumnBool
        periodicStrip (1 : WindowColumn)).toNat
      (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          packed.normalizedColumnBool
            periodicStrip (4 : WindowColumn))).toNat
      (packedNormalizationColumnAtCost
        periodicStrip packed (1 : WindowColumn))
      (packedNormalizationLastThreeCost periodicStrip packed)
      thirdBudget tag1 tagLastThree valuesThird headThird
      headSuccThird cost1Third lastThreeBound (by
        simp only [thirdBudget]
        exact Nat.mul_pos (by norm_num) (Nat.succ_pos _))
    simpa [packedNormalizationLastFourCost, values,
      fourthBudget] using bound
  have valuesFourth : encodedListSpace values ≤ fourthBudget :=
    valuesThird.trans (by simp only [fourthBudget]; omega)
  have headFourth :
      (Computability.encodeNat values.headI).length ≤ fourthBudget :=
    headThird.trans (by simp only [fourthBudget]; omega)
  have headSuccFourth :
      (Computability.encodeNat (values.headI + 1)).length ≤
        fourthBudget :=
    headSuccThird.trans (by simp only [fourthBudget]; omega)
  have cost0Fourth :
      packedNormalizationColumnAtCost
          periodicStrip packed (0 : WindowColumn) ≤ fourthBudget :=
    cost0Base.trans (by
      simp only [fourthBudget, thirdBudget, secondBudget]
      omega)
  have tagLastFour :
      (packed.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
          (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
            packed.normalizedColumnBool
              periodicStrip (4 : WindowColumn)))).toNat ≤ 1 := by
    cases packed.normalizedColumnBool periodicStrip (1 : WindowColumn) <;>
      cases packed.normalizedColumnBool
        periodicStrip (2 : WindowColumn) <;>
      cases packed.normalizedColumnBool
        periodicStrip (3 : WindowColumn) <;>
      cases packed.normalizedColumnBool
        periodicStrip (4 : WindowColumn) <;> simp
  have wholeBound :
      packedNormalizationAllCost periodicStrip packed ≤ finalBudget := by
    have bound := boolAndCost_le_budget values
      (packed.normalizedColumnBool
        periodicStrip (0 : WindowColumn)).toNat
      (packed.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
          (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
            packed.normalizedColumnBool
              periodicStrip (4 : WindowColumn)))).toNat
      (packedNormalizationColumnAtCost
        periodicStrip packed (0 : WindowColumn))
      (packedNormalizationLastFourCost periodicStrip packed)
      fourthBudget tag0 tagLastFour valuesFourth headFourth
      headSuccFourth cost0Fourth lastFourBound (by
        simp only [fourthBudget]
        exact Nat.mul_pos (by norm_num) (Nat.succ_pos _))
    simpa [packedNormalizationAllCost, values,
      finalBudget] using bound
  exact wholeBound.trans (by
    simp only [finalBudget, fourthBudget, thirdBudget,
      secondBudget, baseBudget]
    omega)

end EvaluatorCodeFits

end PartrecToTM2
end Turing

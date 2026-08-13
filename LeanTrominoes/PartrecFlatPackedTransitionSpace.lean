/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecDivisionSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecFlatPackedNormalizationAllSpace
import LeanTrominoes.PartrecFlatPackedCenterLoopSpace
import LeanTrominoes.PartrecFlatPackedOverlapLoopSpace
import LeanTrominoes.PartrecFlatPackedTransition

/-!
# Evaluator-space certificate for the complete flat packed transition

The native transition context already supplies every component with the same
flat fields.  This module fits cyclic phase advance, composes it with the
bounded normalization, center-validity, and overlap evaluators, and gives the
complete transition one common polynomial workspace envelope.
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

def flatPackedTransitionPhaseDivisionArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let successorCost := succCost [current.phase] + getCost 4 values
  prependCost values [current.phase + 1] [periodicStrip.period]
    successorCost (getCost 1 values)

theorem flatPackedTransitionPhaseDivisionArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedTransitionPhaseDivisionArgumentsCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [current.phase + 1, periodicStrip.period]
      (flatPackedTransitionPhaseDivisionArgumentsCost
        periodicStrip current next) := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  have successor := comp (succ_named [current.phase]) (get 4 values)
  have result := prepend successor (get 1 values)
  simpa [Code.flatPackedTransitionPhaseDivisionArgumentsCode,
    flatPackedTransitionPhaseDivisionArgumentsCost,
    Code.flatPackedTransitionContext, prependCost, values] using result

def flatPackedTransitionPhaseRemainderCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  getCost 1
      [(current.phase + 1) / periodicStrip.period,
        (current.phase + 1) % periodicStrip.period] +
    (divisionSpaceBound (current.phase + 1) periodicStrip.period +
      flatPackedTransitionPhaseDivisionArgumentsCost
        periodicStrip current next)

theorem flatPackedTransitionPhaseRemainder
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedTransitionPhaseRemainderCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.phase + 1) % periodicStrip.period]
      (flatPackedTransitionPhaseRemainderCost
        periodicStrip current next) := by
  have divided := comp
    (division (current.phase + 1) periodicStrip.period)
    (flatPackedTransitionPhaseDivisionArguments periodicStrip current next)
  have projected := comp
    (get 1 [(current.phase + 1) / periodicStrip.period,
      (current.phase + 1) % periodicStrip.period]) divided
  simpa [Code.flatPackedTransitionPhaseRemainderCode,
    flatPackedTransitionPhaseRemainderCost] using projected

def flatPackedTransitionPhaseEqualityArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  prependCost values [next.phase]
    [(current.phase + 1) % periodicStrip.period]
    (getCost 6 values)
    (flatPackedTransitionPhaseRemainderCost periodicStrip current next)

theorem flatPackedTransitionPhaseEqualityArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedTransitionPhaseEqualityArgumentsCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [next.phase, (current.phase + 1) % periodicStrip.period]
      (flatPackedTransitionPhaseEqualityArgumentsCost
        periodicStrip current next) := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  have result := prepend (get 6 values)
    (flatPackedTransitionPhaseRemainder periodicStrip current next)
  simpa [Code.flatPackedTransitionPhaseEqualityArgumentsCode,
    flatPackedTransitionPhaseEqualityArgumentsCost,
    Code.flatPackedTransitionContext, prependCost, values] using result

def flatPackedTransitionPhaseCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  natEqCost next.phase
      ((current.phase + 1) % periodicStrip.period) +
    flatPackedTransitionPhaseEqualityArgumentsCost periodicStrip current next

theorem flatPackedTransitionPhase
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    let advances := decide
      (next.phase = (current.phase + 1) % periodicStrip.period)
    EvaluatorCodeFits Code.flatPackedTransitionPhaseCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [advances.toNat]
      (flatPackedTransitionPhaseCost periodicStrip current next) := by
  simp only
  have result := comp
    (natEq next.phase ((current.phase + 1) % periodicStrip.period))
    (flatPackedTransitionPhaseEqualityArguments periodicStrip current next)
  have tagEq :
      (decide (next.phase =
        (current.phase + 1) % periodicStrip.period)).toNat =
      if next.phase =
        (current.phase + 1) % periodicStrip.period then 1 else 0 := by
    by_cases advances :
        next.phase = (current.phase + 1) % periodicStrip.period <;>
      simp [advances]
  rw [tagEq]
  simpa [Code.flatPackedTransitionPhaseCode,
    flatPackedTransitionPhaseCost] using result

def flatPackedTransitionOverlapCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  boolAndCost values phase.toNat columns.toNat
    (flatPackedTransitionPhaseCost periodicStrip current next)
    (flatPackedOverlapColumnsCost periodicStrip current next)

theorem flatPackedTransitionOverlap
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedTransitionOverlapCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.overlapsBool periodicStrip next).toNat]
      (flatPackedTransitionOverlapCost periodicStrip current next) := by
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  have result := boolAnd_fit_bool phase columns
    (by simpa [phase] using
      flatPackedTransitionPhase periodicStrip current next)
    (by simpa [columns] using
      flatPackedOverlapColumns periodicStrip current next)
  change EvaluatorCodeFits Code.flatPackedTransitionOverlapCode
    (Code.flatPackedTransitionContext periodicStrip current next)
    [(phase && columns).toNat] _
  simpa [Code.flatPackedTransitionOverlapCode,
    flatPackedTransitionOverlapCost, phase, columns] using result

def flatPackedTransitionTailCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  boolAndCost values center.toNat overlap.toNat
    (flatPackedCenterValidCost tromino periodicStrip current next)
    (flatPackedTransitionOverlapCost periodicStrip current next)

theorem flatPackedTransitionTail
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd (Code.flatPackedCenterValidCode tromino)
        Code.flatPackedTransitionOverlapCode)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [((current.isCenterValidBool tromino periodicStrip) &&
        current.overlapsBool periodicStrip next).toNat]
      (flatPackedTransitionTailCost tromino periodicStrip current next) := by
  exact boolAnd_fit_bool
    (current.isCenterValidBool tromino periodicStrip)
    (current.overlapsBool periodicStrip next)
    (flatPackedCenterValid tromino periodicStrip wellFormed current next)
    (flatPackedTransitionOverlap periodicStrip current next)

def flatPackedTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let normalized := current.isNormalizedBool periodicStrip
  let tail := current.isCenterValidBool tromino periodicStrip &&
    current.overlapsBool periodicStrip next
  boolAndCost values normalized.toNat tail.toNat
    (flatPackedNormalizationAllCost periodicStrip current next)
    (flatPackedTransitionTailCost tromino periodicStrip current next)

/-- Exact fitted certificate for the complete flat transition evaluator. -/
theorem flatPackedTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedTransitionCode tromino)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.transitionBool tromino periodicStrip next).toNat]
      (flatPackedTransitionCost tromino periodicStrip current next) := by
  let normalized := current.isNormalizedBool periodicStrip
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  have result := boolAnd_fit_bool normalized (center && overlap)
    (by simpa [normalized] using
      flatPackedNormalizationAll periodicStrip current next)
    (by simpa [center, overlap] using
      flatPackedTransitionTail tromino periodicStrip wellFormed current next)
  change EvaluatorCodeFits (Code.flatPackedTransitionCode tromino)
    (Code.flatPackedTransitionContext periodicStrip current next)
    [(normalized && center && overlap).toNat] _
  simpa [Code.flatPackedTransitionCode, flatPackedTransitionCost,
    normalized, center, overlap, Bool.and_assoc] using result

/-! ## Native polynomial bounds -/

/-- The encoded footprint shared by every flat-transition component. -/
def flatPackedTransitionContextUnit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next) + 10

private theorem flatPackedTransitionContextUnit_pos
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    1 ≤ flatPackedTransitionContextUnit periodicStrip current next := by
  simp [flatPackedTransitionContextUnit]

private theorem flatPackedTransitionContextSpace_le_unit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    encodedListSpace
        (Code.flatPackedTransitionContext periodicStrip current next) ≤
      flatPackedTransitionContextUnit periodicStrip current next := by
  simp [flatPackedTransitionContextUnit]

private theorem flatPackedTransitionContextHeadSpace_le_unit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (Computability.encodeNat
        (Code.flatPackedTransitionContext periodicStrip current next).headI).length ≤
      flatPackedTransitionContextUnit periodicStrip current next := by
  have head := listCodeEncodedListSpace_singleton_headI_le
    (Code.flatPackedTransitionContext periodicStrip current next)
  have input := flatPackedTransitionContextSpace_le_unit periodicStrip current next
  have localBound :
      (Computability.encodeNat
        (Code.flatPackedTransitionContext periodicStrip current next).headI).length ≤
      encodedListSpace
        (Code.flatPackedTransitionContext periodicStrip current next) := by
    simpa [encodedListSpace_cons] using head
  exact localBound.trans input

private theorem flatPackedTransitionContextHeadSuccSpace_le_unit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (Computability.encodeNat
        ((Code.flatPackedTransitionContext periodicStrip current next).headI + 1)).length ≤
      flatPackedTransitionContextUnit periodicStrip current next := by
  have head := listCodeEncodedListSpace_singleton_headI_le
    (Code.flatPackedTransitionContext periodicStrip current next)
  have successor := listCodeEncodeNat_succ_length_le
    (Code.flatPackedTransitionContext periodicStrip current next).headI
  have successor' :
      (Computability.encodeNat
        ((Code.flatPackedTransitionContext periodicStrip current next).headI + 1)).length ≤
      (Computability.encodeNat
        (Code.flatPackedTransitionContext periodicStrip current next).headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successor
  simp only [encodedListSpace_cons, encodedListSpace_nil] at head
  simp only [flatPackedTransitionContextUnit]
  omega

private theorem flatPackedTransitionPeriodSpace_le_unit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    encodedListSpace [periodicStrip.period] ≤
      flatPackedTransitionContextUnit periodicStrip current next := by
  have member := flatPackedTransitionScanMemberSpace_le periodicStrip.period
    (Code.flatPackedTransitionContext periodicStrip current next) (by
      simp [Code.flatPackedTransitionContext])
  exact member.trans
    (flatPackedTransitionContextSpace_le_unit periodicStrip current next)

private theorem flatPackedTransitionCurrentPhaseSpace_le_unit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    encodedListSpace [current.phase] ≤
      flatPackedTransitionContextUnit periodicStrip current next := by
  have member := flatPackedTransitionScanMemberSpace_le current.phase
    (Code.flatPackedTransitionContext periodicStrip current next) (by
      simp [Code.flatPackedTransitionContext])
  exact member.trans
    (flatPackedTransitionContextSpace_le_unit periodicStrip current next)

private theorem flatPackedTransitionNextPhaseSpace_le_unit
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    encodedListSpace [next.phase] ≤
      flatPackedTransitionContextUnit periodicStrip current next := by
  have member := flatPackedTransitionScanMemberSpace_le next.phase
    (Code.flatPackedTransitionContext periodicStrip current next) (by
      simp [Code.flatPackedTransitionContext])
  exact member.trans
    (flatPackedTransitionContextSpace_le_unit periodicStrip current next)

private theorem flatPackedTransitionPhaseDivisionArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseDivisionArgumentsCost periodicStrip current next ≤
      1000000 * flatPackedTransitionContextUnit
        periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedTransitionContextUnit periodicStrip current next
  have inputSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using
      flatPackedTransitionContextSpace_le_unit periodicStrip current next
  have currentSpace : encodedListSpace [current.phase] ≤ unit := by
    simpa [unit] using
      flatPackedTransitionCurrentPhaseSpace_le_unit periodicStrip current next
  have periodSpace : encodedListSpace [periodicStrip.period] ≤ unit := by
    simpa [unit] using
      flatPackedTransitionPeriodSpace_le_unit periodicStrip current next
  have unitLarge : 10 ≤ unit := by
    simp [unit, flatPackedTransitionContextUnit]
  have currentSuccBits := encodeNat_succ_length_le current.phase
  have currentSuccBits' :
      (Computability.encodeNat (current.phase + 1)).length ≤
        (Computability.encodeNat current.phase).length + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccBits
  have currentSuccSpace : encodedListSpace [current.phase + 1] ≤ 2 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at currentSpace ⊢
    omega
  have outputSpace :
      encodedListSpace [current.phase + 1, periodicStrip.period] ≤
        4 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at currentSuccSpace periodSpace ⊢
    omega
  have get4Raw := listCodeGetCost_le_linear 4 values
  have get1Raw := listCodeGetCost_le_linear 1 values
  have get4 : getCost 4 values ≤ 100000 * unit := by
    calc
      getCost 4 values ≤ (10000 * (4 + 1)) *
          (encodedListSpace values + 1) := get4Raw
      _ ≤ 100000 * unit := by omega
  have get1 : getCost 1 values ≤ 100000 * unit := by
    calc
      getCost 1 values ≤ (10000 * (1 + 1)) *
          (encodedListSpace values + 1) := get1Raw
      _ ≤ 100000 * unit := by omega
  have successorRaw := succCost_le [current.phase]
  have successor : succCost [current.phase] ≤ 100000 * unit := by
    exact successorRaw.trans (by omega)
  have estimate := listCodePrependCost_le_of values [current.phase + 1]
    [periodicStrip.period] (succCost [current.phase] + getCost 4 values)
    (getCost 1 values) (4 * unit) (by omega) (by omega) (by
      simpa only [List.headI_cons] using outputSpace)
  change prependCost values [current.phase + 1] [periodicStrip.period]
      (succCost [current.phase] + getCost 4 values) (getCost 1 values) ≤ _
  omega

private theorem flatPackedTransitionDivisionCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    divisionSpaceBound (current.phase + 1) periodicStrip.period ≤
      1000000000000000 * flatPackedTransitionContextUnit
        periodicStrip current next := by
  let unit := flatPackedTransitionContextUnit periodicStrip current next
  have currentSpace := flatPackedTransitionCurrentPhaseSpace_le_unit
    periodicStrip current next
  have periodSpace := flatPackedTransitionPeriodSpace_le_unit
    periodicStrip current next
  have currentBits :
      (Computability.encodeNat current.phase).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at currentSpace
    omega
  have periodBits :
      (Computability.encodeNat periodicStrip.period).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at periodSpace
    omega
  have currentSuccRaw := encodeNat_succ_length_le current.phase
  have currentSuccBits :
      (Computability.encodeNat (current.phase + 1)).length ≤ unit + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccRaw.trans (by omega)
  have sumBits := encodeNat_add_length_le_sum
    (current.phase + 1) periodicStrip.period
  have scaledBits := encodeNat_mul_length_le_sum 8
    (current.phase + 1 + periodicStrip.period)
  have finalBits := encodeNat_add_length_le_sum
    (8 * (current.phase + 1 + periodicStrip.period)) 16
  have eightBits : (Computability.encodeNat 8).length = 4 := by native_decide
  have sixteenBits : (Computability.encodeNat 16).length = 5 := by native_decide
  have unitLarge : 10 ≤ unit := by
    simp [unit, flatPackedTransitionContextUnit]
  simp only [divisionSpaceBound, encodedListSpace_cons,
    encodedListSpace_nil]
  omega

private theorem flatPackedTransitionPhaseRemainderCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseRemainderCost periodicStrip current next ≤
      100000000000000000 * flatPackedTransitionContextUnit
        periodicStrip current next := by
  let unit := flatPackedTransitionContextUnit periodicStrip current next
  let output := [(current.phase + 1) / periodicStrip.period,
    (current.phase + 1) % periodicStrip.period]
  have currentSpace := flatPackedTransitionCurrentPhaseSpace_le_unit
    periodicStrip current next
  have currentBits :
      (Computability.encodeNat current.phase).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at currentSpace
    omega
  have currentSuccRaw := encodeNat_succ_length_le current.phase
  have currentSuccBits :
      (Computability.encodeNat (current.phase + 1)).length ≤ unit + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccRaw.trans (by omega)
  have quotientBits := encodeNat_length_mono
    (Nat.div_le_self (current.phase + 1) periodicStrip.period)
  have remainderBits := encodeNat_length_mono
    (Nat.mod_le (current.phase + 1) periodicStrip.period)
  have unitLarge : 10 ≤ unit := by
    simp [unit, flatPackedTransitionContextUnit]
  have outputSpace : encodedListSpace output ≤ 4 * unit := by
    simp only [output, encodedListSpace_cons, encodedListSpace_nil]
    omega
  have projectionRaw := listCodeGetCost_le_linear 1 output
  have projection : getCost 1 output ≤ 100000 * unit := by
    exact projectionRaw.trans (by omega)
  have division := flatPackedTransitionDivisionCost_le_linear
    periodicStrip current next
  have arguments := flatPackedTransitionPhaseDivisionArgumentsCost_le_linear
    periodicStrip current next
  change getCost 1 output +
      (divisionSpaceBound (current.phase + 1) periodicStrip.period +
        flatPackedTransitionPhaseDivisionArgumentsCost
          periodicStrip current next) ≤ _
  omega

private theorem flatPackedTransitionPhaseEqualityArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseEqualityArgumentsCost periodicStrip current next ≤
      10000000000000000000 * flatPackedTransitionContextUnit
        periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedTransitionContextUnit periodicStrip current next
  let remainder := (current.phase + 1) % periodicStrip.period
  have inputSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using
      flatPackedTransitionContextSpace_le_unit periodicStrip current next
  have nextSpace : encodedListSpace [next.phase] ≤ unit := by
    simpa [unit] using
      flatPackedTransitionNextPhaseSpace_le_unit periodicStrip current next
  have currentSpace := flatPackedTransitionCurrentPhaseSpace_le_unit
    periodicStrip current next
  have currentBits :
      (Computability.encodeNat current.phase).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at currentSpace
    omega
  have currentSuccRaw := encodeNat_succ_length_le current.phase
  have currentSuccBits :
      (Computability.encodeNat (current.phase + 1)).length ≤ unit + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccRaw.trans (by omega)
  have remainderBitsRaw := encodeNat_length_mono
    (Nat.mod_le (current.phase + 1) periodicStrip.period)
  have remainderBits :
      (Computability.encodeNat remainder).length ≤
        (Computability.encodeNat (current.phase + 1)).length := by
    simpa [remainder] using remainderBitsRaw
  have unitLarge : 10 ≤ unit := by
    simp [unit, flatPackedTransitionContextUnit]
  have remainderSpace : encodedListSpace [remainder] ≤ 2 * unit := by
    simp only [remainder, encodedListSpace_cons, encodedListSpace_nil]
    omega
  have outputSpace : encodedListSpace [next.phase, remainder] ≤ 4 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at nextSpace remainderSpace ⊢
    omega
  have get6Raw := listCodeGetCost_le_linear 6 values
  have get6 : getCost 6 values ≤ 100000 * unit := by
    exact get6Raw.trans (by omega)
  have remainderCost := flatPackedTransitionPhaseRemainderCost_le_linear
    periodicStrip current next
  have estimate := listCodePrependCost_le_of values [next.phase] [remainder]
    (getCost 6 values)
    (flatPackedTransitionPhaseRemainderCost periodicStrip current next)
    (4 * unit) (by omega) (by omega) (by
      simpa only [List.headI_cons] using outputSpace)
  change prependCost values [next.phase] [remainder] (getCost 6 values)
      (flatPackedTransitionPhaseRemainderCost periodicStrip current next) ≤ _
  omega

/-- A linear native-context bound for the cyclic phase computation. -/
def flatPackedTransitionPhaseSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  100000000000000000000000000000000 *
    flatPackedTransitionContextUnit periodicStrip current next

theorem flatPackedTransitionPhaseCost_le_bound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseCost periodicStrip current next ≤
      flatPackedTransitionPhaseSpaceBound periodicStrip current next := by
  let unit := flatPackedTransitionContextUnit periodicStrip current next
  let remainder := (current.phase + 1) % periodicStrip.period
  have equalityRaw := natEqCost_le_linear next.phase remainder
  have nextSpace := flatPackedTransitionNextPhaseSpace_le_unit
    periodicStrip current next
  have currentSpace := flatPackedTransitionCurrentPhaseSpace_le_unit
    periodicStrip current next
  have nextBits : (Computability.encodeNat next.phase).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at nextSpace
    omega
  have currentBits : (Computability.encodeNat current.phase).length ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at currentSpace
    omega
  have currentSuccRaw := encodeNat_succ_length_le current.phase
  have currentSuccBits :
      (Computability.encodeNat (current.phase + 1)).length ≤ unit + 1 := by
    simpa [Nat.succ_eq_add_one] using currentSuccRaw.trans (by omega)
  have remainderBitsRaw := encodeNat_length_mono
    (Nat.mod_le (current.phase + 1) periodicStrip.period)
  have remainderBits :
      (Computability.encodeNat remainder).length ≤
        (Computability.encodeNat (current.phase + 1)).length := by
    simpa [remainder] using remainderBitsRaw
  have sumBits := encodeNat_add_length_le_sum next.phase remainder
  have scaledBits := encodeNat_mul_length_le_sum 2 (next.phase + remainder)
  have finalBits := encodeNat_add_length_le_sum
    (2 * (next.phase + remainder)) 4
  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  have unitLarge : 10 ≤ unit := by
    simp [unit, flatPackedTransitionContextUnit]
  have equality : natEqCost next.phase remainder ≤
      1000000000000 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at equalityRaw
    omega
  have arguments := flatPackedTransitionPhaseEqualityArgumentsCost_le_linear
    periodicStrip current next
  have equality' : natEqCost next.phase
      ((current.phase + 1) % periodicStrip.period) ≤
        1000000000000 * unit := by
    simpa [remainder] using equality
  simp only [flatPackedTransitionPhaseCost, flatPackedTransitionPhaseSpaceBound]
  omega

theorem flatPackedTransitionPhaseBounded
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    let advances := decide
      (next.phase = (current.phase + 1) % periodicStrip.period)
    EvaluatorCodeFits Code.flatPackedTransitionPhaseCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [advances.toNat]
      (flatPackedTransitionPhaseSpaceBound periodicStrip current next) := by
  simp only
  exact (flatPackedTransitionPhase periodicStrip current next).mono
    (flatPackedTransitionPhaseCost_le_bound periodicStrip current next)

/-- A common allowance for the four semantic components of a transition. -/
def flatPackedTransitionComponentSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  flatPackedNormalizationAllSpaceBound periodicStrip current next +
    flatPackedCenterValidSpaceBound periodicStrip current next +
    flatPackedOverlapColumnsSpaceBound periodicStrip current next +
    flatPackedTransitionPhaseSpaceBound periodicStrip current next +
    flatPackedTransitionContextUnit periodicStrip current next + 1

/-- The phase/column conjunction adds one fixed Boolean layer. -/
def flatPackedTransitionOverlapSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  1000 *
    (flatPackedTransitionComponentSpaceBound periodicStrip current next + 1)

/-- The center/overlap conjunction adds the second Boolean layer. -/
def flatPackedTransitionTailSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  1000 *
    (flatPackedTransitionOverlapSpaceBound periodicStrip current next + 1)

/-- Explicit native polynomial workspace bound for the complete flat packed
transition predicate. -/
def flatPackedTransitionSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  1000 *
    (flatPackedTransitionTailSpaceBound periodicStrip current next + 1)

private theorem flatPackedTransitionComponentSpaceBound_pos
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    1 ≤ flatPackedTransitionComponentSpaceBound
      periodicStrip current next := by
  simp [flatPackedTransitionComponentSpaceBound]

private theorem flatPackedTransitionContextSpace_le_component
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    encodedListSpace
        (Code.flatPackedTransitionContext periodicStrip current next) ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have context := flatPackedTransitionContextSpace_le_unit
    periodicStrip current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

private theorem flatPackedTransitionContextHeadSpace_le_component
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (Computability.encodeNat
        (Code.flatPackedTransitionContext periodicStrip current next).headI).length ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have head := flatPackedTransitionContextHeadSpace_le_unit
    periodicStrip current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

private theorem flatPackedTransitionContextHeadSuccSpace_le_component
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    (Computability.encodeNat
        ((Code.flatPackedTransitionContext periodicStrip current next).headI + 1)).length ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have head := flatPackedTransitionContextHeadSuccSpace_le_unit
    periodicStrip current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

private theorem flatPackedTransitionNormalizationCost_le_component
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationAllCost periodicStrip current next ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have normalization := flatPackedNormalizationAllCost_le_bound
    periodicStrip current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

private theorem flatPackedTransitionCenterCost_le_component
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    flatPackedCenterValidCost tromino periodicStrip current next ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have center := flatPackedCenterValidCost_le_bound tromino periodicStrip
    wellFormed current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

private theorem flatPackedTransitionColumnsCost_le_component
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapColumnsCost periodicStrip current next ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have columns := flatPackedOverlapColumnsCost_le_bound
    periodicStrip current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

private theorem flatPackedTransitionPhaseCost_le_component
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseCost periodicStrip current next ≤
      flatPackedTransitionComponentSpaceBound
        periodicStrip current next := by
  have phase := flatPackedTransitionPhaseCost_le_bound
    periodicStrip current next
  simp only [flatPackedTransitionComponentSpaceBound]
  omega

theorem flatPackedTransitionOverlapCost_le_bound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionOverlapCost periodicStrip current next ≤
      flatPackedTransitionOverlapSpaceBound
        periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  let budget := flatPackedTransitionComponentSpaceBound
    periodicStrip current next
  have valuesBound : encodedListSpace values ≤ budget := by
    simpa [values, budget] using
      flatPackedTransitionContextSpace_le_component periodicStrip current next
  have headBound :
      (Computability.encodeNat values.headI).length ≤ budget := by
    simpa [values, budget] using
      flatPackedTransitionContextHeadSpace_le_component periodicStrip current next
  have headSuccBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    simpa [values, budget] using
      flatPackedTransitionContextHeadSuccSpace_le_component
        periodicStrip current next
  have phaseCost :
      flatPackedTransitionPhaseCost periodicStrip current next ≤ budget := by
    simpa [budget] using
      flatPackedTransitionPhaseCost_le_component periodicStrip current next
  have columnsCost :
      flatPackedOverlapColumnsCost periodicStrip current next ≤ budget := by
    simpa [budget] using
      flatPackedTransitionColumnsCost_le_component periodicStrip current next
  have positive : 1 ≤ budget := by
    simpa [budget] using
      flatPackedTransitionComponentSpaceBound_pos periodicStrip current next
  have bound := boolAndCost_le_budget values phase.toNat columns.toNat
    (flatPackedTransitionPhaseCost periodicStrip current next)
    (flatPackedOverlapColumnsCost periodicStrip current next)
    budget (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
    headSuccBound phaseCost columnsCost positive
  simpa [flatPackedTransitionOverlapCost,
    flatPackedTransitionOverlapSpaceBound,
    values, phase, columns, budget] using bound

private theorem flatPackedTransitionTailCost_le_bound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    flatPackedTransitionTailCost tromino periodicStrip current next ≤
      flatPackedTransitionTailSpaceBound periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  let componentBudget := flatPackedTransitionComponentSpaceBound
    periodicStrip current next
  let budget := flatPackedTransitionOverlapSpaceBound
    periodicStrip current next
  have componentPositive : 1 ≤ componentBudget := by
    simpa [componentBudget] using
      flatPackedTransitionComponentSpaceBound_pos periodicStrip current next
  have componentLe : componentBudget ≤ budget := by
    simp only [budget, flatPackedTransitionOverlapSpaceBound]
    omega
  have valuesBound : encodedListSpace values ≤ budget := by
    have raw := flatPackedTransitionContextSpace_le_component
      periodicStrip current next
    have raw' : encodedListSpace values ≤ componentBudget := by
      simpa [values, componentBudget] using raw
    exact raw'.trans componentLe
  have headBound :
      (Computability.encodeNat values.headI).length ≤ budget := by
    have raw := flatPackedTransitionContextHeadSpace_le_component
      periodicStrip current next
    have raw' : (Computability.encodeNat values.headI).length ≤
        componentBudget := by
      simpa [values, componentBudget] using raw
    exact raw'.trans componentLe
  have headSuccBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    have raw := flatPackedTransitionContextHeadSuccSpace_le_component
      periodicStrip current next
    have raw' : (Computability.encodeNat (values.headI + 1)).length ≤
        componentBudget := by
      simpa [values, componentBudget] using raw
    exact raw'.trans componentLe
  have centerCost :
      flatPackedCenterValidCost tromino periodicStrip current next ≤ budget :=
    (by
      have raw := flatPackedTransitionCenterCost_le_component tromino
        periodicStrip wellFormed current next
      have raw' :
          flatPackedCenterValidCost tromino periodicStrip current next ≤
            componentBudget := by
        simpa [componentBudget] using raw
      exact raw'.trans componentLe)
  have overlapCost :
      flatPackedTransitionOverlapCost periodicStrip current next ≤ budget := by
    simpa [budget] using
      flatPackedTransitionOverlapCost_le_bound periodicStrip current next
  have positive : 1 ≤ budget := componentPositive.trans componentLe
  have bound := boolAndCost_le_budget values center.toNat overlap.toNat
    (flatPackedCenterValidCost tromino periodicStrip current next)
    (flatPackedTransitionOverlapCost periodicStrip current next)
    budget (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
    headSuccBound centerCost overlapCost positive
  simpa [flatPackedTransitionTailCost, flatPackedTransitionTailSpaceBound,
    values, center, overlap, componentBudget, budget] using bound

theorem flatPackedTransitionCost_le_bound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    flatPackedTransitionCost tromino periodicStrip current next ≤
      flatPackedTransitionSpaceBound periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let normalized := current.isNormalizedBool periodicStrip
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  let componentBudget := flatPackedTransitionComponentSpaceBound
    periodicStrip current next
  let overlapBudget := flatPackedTransitionOverlapSpaceBound
    periodicStrip current next
  let budget := flatPackedTransitionTailSpaceBound periodicStrip current next
  have componentPositive : 1 ≤ componentBudget := by
    simpa [componentBudget] using
      flatPackedTransitionComponentSpaceBound_pos periodicStrip current next
  have componentLeOverlap : componentBudget ≤ overlapBudget := by
    simp only [overlapBudget, flatPackedTransitionOverlapSpaceBound]
    omega
  have overlapPositive : 1 ≤ overlapBudget :=
    componentPositive.trans componentLeOverlap
  have overlapLe : overlapBudget ≤ budget := by
    simp only [budget, flatPackedTransitionTailSpaceBound]
    omega
  have componentLe : componentBudget ≤ budget :=
    componentLeOverlap.trans overlapLe
  have valuesBound : encodedListSpace values ≤ budget := by
    have raw := flatPackedTransitionContextSpace_le_component
      periodicStrip current next
    have raw' : encodedListSpace values ≤ componentBudget := by
      simpa [values, componentBudget] using raw
    exact raw'.trans componentLe
  have headBound :
      (Computability.encodeNat values.headI).length ≤ budget := by
    have raw := flatPackedTransitionContextHeadSpace_le_component
      periodicStrip current next
    have raw' : (Computability.encodeNat values.headI).length ≤
        componentBudget := by
      simpa [values, componentBudget] using raw
    exact raw'.trans componentLe
  have headSuccBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    have raw := flatPackedTransitionContextHeadSuccSpace_le_component
      periodicStrip current next
    have raw' : (Computability.encodeNat (values.headI + 1)).length ≤
        componentBudget := by
      simpa [values, componentBudget] using raw
    exact raw'.trans componentLe
  have normalizationCost :
      flatPackedNormalizationAllCost periodicStrip current next ≤ budget := by
    have raw := flatPackedTransitionNormalizationCost_le_component
      periodicStrip current next
    have raw' : flatPackedNormalizationAllCost periodicStrip current next ≤
        componentBudget := by
      simpa [componentBudget] using raw
    exact raw'.trans componentLe
  have tailCost :
      flatPackedTransitionTailCost tromino periodicStrip current next ≤ budget := by
    simpa [budget] using
      flatPackedTransitionTailCost_le_bound tromino periodicStrip wellFormed
        current next
  have positive : 1 ≤ budget := overlapPositive.trans overlapLe
  have bound := boolAndCost_le_budget values normalized.toNat
    (center && overlap).toNat
    (flatPackedNormalizationAllCost periodicStrip current next)
    (flatPackedTransitionTailCost tromino periodicStrip current next)
    budget (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
    headSuccBound normalizationCost tailCost positive
  simpa [flatPackedTransitionCost, flatPackedTransitionSpaceBound,
    values, normalized, center, overlap, componentBudget, overlapBudget,
    budget, Bool.and_assoc] using bound

/-- The complete flat packed transition evaluator, including phase advance,
normalization, center validity, and all shared-column checks, runs within the
native polynomial workspace bound. -/
theorem flatPackedTransitionBounded
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedTransitionCode tromino)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.transitionBool tromino periodicStrip next).toNat]
      (flatPackedTransitionSpaceBound periodicStrip current next) :=
  (flatPackedTransition tromino periodicStrip wellFormed current next).mono
    (flatPackedTransitionCost_le_bound tromino periodicStrip wellFormed
      current next)

/-! ## Context-unit-only envelope -/

/-- The complete transition bound with its semantic context replaced by a
single numeric footprint.  This exposes the fixed polynomial used by callers
that have already bounded the reconstructed transition context. -/
def flatPackedTransitionSpaceEnvelope (unit : Nat) : Nat :=
  let normalizationBody :=
    10000000000000000000000000000000000000000000000000000000000000000000000000000000000 *
      unit ^ 2
  let normalizationColumn :=
    200000 * (normalizationBody * unit + unit + 1)
  let normalizationLastTwo := 1000 * (normalizationColumn + 1)
  let normalizationLastThree := 1000 * (normalizationLastTwo + 1)
  let normalizationLastFour := 1000 * (normalizationLastThree + 1)
  let normalizationAll := 1000 * (normalizationLastFour + 1)
  let centerBody := (10 ^ 1100) * unit ^ 2
  let centerValid := 200000 * (centerBody * unit + unit + 1)
  let overlapBody := (10 ^ 1100) * unit ^ 2
  let overlapColumn := 200000 * (overlapBody * unit + unit + 1)
  let overlapLastTwo := 1000 * (overlapColumn + 1)
  let overlapLastThree := 1000 * (overlapLastTwo + 1)
  let overlapColumns := 1000 * (overlapLastThree + 1)
  let phase := 100000000000000000000000000000000 * unit
  let component :=
    normalizationAll + centerValid + overlapColumns + phase + unit + 1
  let overlap := 1000 * (component + 1)
  let tail := 1000 * (overlap + 1)
  1000 * (tail + 1)

theorem flatPackedTransitionSpaceBound_eq_envelope
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionSpaceBound periodicStrip current next =
      flatPackedTransitionSpaceEnvelope
        (flatPackedTransitionContextUnit periodicStrip current next) := by
  rfl

theorem flatPackedTransitionSpaceEnvelope_mono
    {first second : Nat} (bounded : first ≤ second) :
    flatPackedTransitionSpaceEnvelope first ≤
      flatPackedTransitionSpaceEnvelope second := by
  simp only [flatPackedTransitionSpaceEnvelope]
  gcongr

end EvaluatorCodeFits
end PartrecToTM2
end Turing

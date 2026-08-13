/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedNormalizationLoopSpace
import LeanTrominoes.PartrecFlatPackedNormalizationAll

/-!
# Evaluator-space certificate for all five flat normalization columns

The five already bounded motif scans share the native transition context.
This module fits their fixed Boolean conjunction and lifts the common column
bound through its four conjunction nodes.
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

def flatPackedNormalizationAllCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let b0 := current.normalizedColumnBool periodicStrip (0 : WindowColumn)
  let b1 := current.normalizedColumnBool periodicStrip (1 : WindowColumn)
  let b2 := current.normalizedColumnBool periodicStrip (2 : WindowColumn)
  let b3 := current.normalizedColumnBool periodicStrip (3 : WindowColumn)
  let b4 := current.normalizedColumnBool periodicStrip (4 : WindowColumn)
  let cost34 := boolAndCost values b3.toNat b4.toNat
    (flatPackedNormalizationColumnCost (3 : WindowColumn) periodicStrip
      current next)
    (flatPackedNormalizationColumnCost (4 : WindowColumn) periodicStrip
      current next)
  let cost234 := boolAndCost values b2.toNat (b3 && b4).toNat
    (flatPackedNormalizationColumnCost (2 : WindowColumn) periodicStrip
      current next) cost34
  let cost1234 := boolAndCost values b1.toNat (b2 && b3 && b4).toNat
    (flatPackedNormalizationColumnCost (1 : WindowColumn) periodicStrip
      current next) cost234
  boolAndCost values b0.toNat (b1 && b2 && b3 && b4).toNat
    (flatPackedNormalizationColumnCost (0 : WindowColumn) periodicStrip
      current next) cost1234

theorem flatPackedNormalizationAll
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedNormalizationAllCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.isNormalizedBool periodicStrip).toNat]
      (flatPackedNormalizationAllCost periodicStrip current next) := by
  let b0 := current.normalizedColumnBool periodicStrip (0 : WindowColumn)
  let b1 := current.normalizedColumnBool periodicStrip (1 : WindowColumn)
  let b2 := current.normalizedColumnBool periodicStrip (2 : WindowColumn)
  let b3 := current.normalizedColumnBool periodicStrip (3 : WindowColumn)
  let b4 := current.normalizedColumnBool periodicStrip (4 : WindowColumn)
  have fit34 := boolAnd_fit_bool b3 b4
    (flatPackedNormalizationColumn (3 : WindowColumn) periodicStrip current next)
    (flatPackedNormalizationColumn (4 : WindowColumn) periodicStrip current next)
  have fit234 := boolAnd_fit_bool b2 (b3 && b4)
    (flatPackedNormalizationColumn (2 : WindowColumn) periodicStrip current next)
    fit34
  have fit1234 := boolAnd_fit_bool b1 (b2 && b3 && b4)
    (flatPackedNormalizationColumn (1 : WindowColumn) periodicStrip current next)
    (by simpa [Bool.and_assoc] using fit234)
  have fitAll := boolAnd_fit_bool b0 (b1 && b2 && b3 && b4)
    (flatPackedNormalizationColumn (0 : WindowColumn) periodicStrip current next)
    (by simpa [Bool.and_assoc] using fit1234)
  have columns : (List.finRange 5 : List (Fin 5)) = [0, 1, 2, 3, 4] := by
    native_decide
  rw [PackedWindowState.isNormalizedBool, columns]
  simpa [Code.flatPackedNormalizationAllCode,
    flatPackedNormalizationAllCost, b0, b1, b2, b3, b4,
    Bool.and_assoc] using fitAll

def flatPackedNormalizationAllSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let columnBound := flatPackedNormalizationColumnSpaceBound periodicStrip
    current next
  let lastTwoBound := 1000 * (columnBound + 1)
  let lastThreeBound := 1000 * (lastTwoBound + 1)
  let lastFourBound := 1000 * (lastThreeBound + 1)
  1000 * (lastFourBound + 1)

theorem flatPackedNormalizationAllCost_le_bound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationAllCost periodicStrip current next ≤
      flatPackedNormalizationAllSpaceBound periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let columnBound := flatPackedNormalizationColumnSpaceBound periodicStrip
    current next
  let lastTwoBound := 1000 * (columnBound + 1)
  let lastThreeBound := 1000 * (lastTwoBound + 1)
  let lastFourBound := 1000 * (lastThreeBound + 1)
  let b0 := current.normalizedColumnBool periodicStrip (0 : WindowColumn)
  let b1 := current.normalizedColumnBool periodicStrip (1 : WindowColumn)
  let b2 := current.normalizedColumnBool periodicStrip (2 : WindowColumn)
  let b3 := current.normalizedColumnBool periodicStrip (3 : WindowColumn)
  let b4 := current.normalizedColumnBool periodicStrip (4 : WindowColumn)
  let cost34 := boolAndCost values b3.toNat b4.toNat
    (flatPackedNormalizationColumnCost (3 : WindowColumn) periodicStrip
      current next)
    (flatPackedNormalizationColumnCost (4 : WindowColumn) periodicStrip
      current next)
  let cost234 := boolAndCost values b2.toNat (b3 && b4).toNat
    (flatPackedNormalizationColumnCost (2 : WindowColumn) periodicStrip
      current next) cost34
  let cost1234 := boolAndCost values b1.toNat (b2 && b3 && b4).toNat
    (flatPackedNormalizationColumnCost (1 : WindowColumn) periodicStrip
      current next) cost234
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedNormalizationContextUnit]
  have contextSpace : encodedListSpace values + 1 ≤ unit := by
    simp [values, unit, flatPackedNormalizationContextUnit]
  have unitToColumn : unit ≤ columnBound := by
    simp only [unit, columnBound, flatPackedNormalizationColumnSpaceBound]
    omega
  have valuesBound : encodedListSpace values ≤ columnBound := by omega
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBound : (Computability.encodeNat values.headI).length ≤
      columnBound := by
    have localBound : (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans valuesBound
  have successor := listCodeEncodeNat_succ_length_le values.headI
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ columnBound := by
    have localBound :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using successor
    have headPlus : (Computability.encodeNat values.headI).length + 1 ≤
        encodedListSpace values + 1 := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans (headPlus.trans (contextSpace.trans unitToColumn))
  have columnPositive : 1 ≤ columnBound := by omega
  have cost0 := flatPackedNormalizationColumnCost_le_bound
    (0 : WindowColumn) periodicStrip current next
  have cost1 := flatPackedNormalizationColumnCost_le_bound
    (1 : WindowColumn) periodicStrip current next
  have cost2 := flatPackedNormalizationColumnCost_le_bound
    (2 : WindowColumn) periodicStrip current next
  have cost3 := flatPackedNormalizationColumnCost_le_bound
    (3 : WindowColumn) periodicStrip current next
  have cost4 := flatPackedNormalizationColumnCost_le_bound
    (4 : WindowColumn) periodicStrip current next
  have bound34 : cost34 ≤ lastTwoBound := by
    have bound := boolAndCost_le_budget values b3.toNat b4.toNat
      (flatPackedNormalizationColumnCost (3 : WindowColumn) periodicStrip
        current next)
      (flatPackedNormalizationColumnCost (4 : WindowColumn) periodicStrip
        current next)
      columnBound (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
      headSuccessorBound cost3 cost4 columnPositive
    simpa [cost34, b3, b4, lastTwoBound] using bound
  have valuesTwo : encodedListSpace values ≤ lastTwoBound :=
    valuesBound.trans (by simp only [lastTwoBound]; omega)
  have headTwo : (Computability.encodeNat values.headI).length ≤
      lastTwoBound := headBound.trans (by simp only [lastTwoBound]; omega)
  have headSuccTwo : (Computability.encodeNat (values.headI + 1)).length ≤
      lastTwoBound :=
    headSuccessorBound.trans (by simp only [lastTwoBound]; omega)
  have cost2Two : flatPackedNormalizationColumnCost (2 : WindowColumn)
      periodicStrip current next ≤ lastTwoBound :=
    cost2.trans (by simp only [lastTwoBound]; omega)
  have twoPositive : 1 ≤ lastTwoBound := by
    simp only [lastTwoBound]
    omega
  have bound234 : cost234 ≤ lastThreeBound := by
    have bound := boolAndCost_le_budget values b2.toNat (b3 && b4).toNat
      (flatPackedNormalizationColumnCost (2 : WindowColumn) periodicStrip
        current next) cost34 lastTwoBound (Bool.toNat_le _) (Bool.toNat_le _)
      valuesTwo headTwo headSuccTwo cost2Two bound34 twoPositive
    simpa [cost234, b2, b3, b4, lastThreeBound] using bound
  have valuesThree : encodedListSpace values ≤ lastThreeBound :=
    valuesTwo.trans (by simp only [lastThreeBound]; omega)
  have headThree : (Computability.encodeNat values.headI).length ≤
      lastThreeBound := headTwo.trans (by simp only [lastThreeBound]; omega)
  have headSuccThree :
      (Computability.encodeNat (values.headI + 1)).length ≤ lastThreeBound :=
    headSuccTwo.trans (by simp only [lastThreeBound]; omega)
  have cost1Three : flatPackedNormalizationColumnCost (1 : WindowColumn)
      periodicStrip current next ≤ lastThreeBound :=
    cost1.trans (by simp only [lastThreeBound, lastTwoBound]; omega)
  have threePositive : 1 ≤ lastThreeBound := by
    simp only [lastThreeBound]
    omega
  have bound1234 : cost1234 ≤ lastFourBound := by
    have bound := boolAndCost_le_budget values b1.toNat
      (b2 && b3 && b4).toNat
      (flatPackedNormalizationColumnCost (1 : WindowColumn) periodicStrip
        current next) cost234 lastThreeBound (Bool.toNat_le _)
      (Bool.toNat_le _) valuesThree headThree headSuccThree cost1Three
      bound234 threePositive
    simpa [cost1234, b1, b2, b3, b4, lastFourBound,
      Bool.and_assoc] using bound
  have valuesFour : encodedListSpace values ≤ lastFourBound :=
    valuesThree.trans (by simp only [lastFourBound]; omega)
  have headFour : (Computability.encodeNat values.headI).length ≤
      lastFourBound := headThree.trans (by simp only [lastFourBound]; omega)
  have headSuccFour :
      (Computability.encodeNat (values.headI + 1)).length ≤ lastFourBound :=
    headSuccThree.trans (by simp only [lastFourBound]; omega)
  have cost0Four : flatPackedNormalizationColumnCost (0 : WindowColumn)
      periodicStrip current next ≤ lastFourBound :=
    cost0.trans (by
      simp only [lastFourBound, lastThreeBound, lastTwoBound]
      omega)
  have fourPositive : 1 ≤ lastFourBound := by
    change 1 ≤ 1000 * (lastThreeBound + 1)
    have h1000 : 1 ≤ 1000 := by decide
    have hfactor : 1 ≤ lastThreeBound + 1 := by
      simpa only [Nat.succ_eq_add_one] using
        Nat.succ_le_succ (Nat.zero_le lastThreeBound)
    exact h1000.trans (by
      simpa using Nat.mul_le_mul_left 1000 hfactor)
  have whole := boolAndCost_le_budget values b0.toNat
    (b1 && b2 && b3 && b4).toNat
    (flatPackedNormalizationColumnCost (0 : WindowColumn) periodicStrip
      current next) cost1234 lastFourBound (Bool.toNat_le _) (Bool.toNat_le _)
    valuesFour headFour headSuccFour cost0Four bound1234 fourPositive
  simpa [flatPackedNormalizationAllCost,
    flatPackedNormalizationAllSpaceBound, values, columnBound, lastTwoBound,
    lastThreeBound, lastFourBound, b0, b1, b2, b3, b4, cost34, cost234,
    cost1234, Bool.and_assoc] using whole

theorem flatPackedNormalizationAllBounded
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedNormalizationAllCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.isNormalizedBool periodicStrip).toNat]
      (flatPackedNormalizationAllSpaceBound periodicStrip current next) :=
  (flatPackedNormalizationAll periodicStrip current next).mono
    (flatPackedNormalizationAllCost_le_bound periodicStrip current next)

end EvaluatorCodeFits
end PartrecToTM2
end Turing

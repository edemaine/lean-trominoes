/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedCenterCandidateSpace
import LeanTrominoes.PartrecFlatPackedCenterSymmetries

/-!
# Evaluator-space certificate for all flat packed center symmetries

This file fits the fixed eight-way center-containment conjunction by composing
the fitted candidate leaves.  The more general list-indexed helper makes the
cost recurrence transparent; the exported program specializes it to the
constant list of all square symmetries.
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
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolAnd leftCode rightCode) values
      [(left && right).toNat]
      (boolAndCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolAnd leftFit rightFit
  cases left <;> cases right <;> simpa using combined

/-- Exact evaluator cost of the fixed-list symmetry conjunction. -/
def flatPackedCenterSymmetryListInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List SquareSymmetry -> Nat
  | [] => oneCost
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
  | symmetry :: symmetries =>
      let values :=
        Code.flatPackedCenterCandidateInput periodicStrip packed base
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      boolAndCost values head.toNat tail.toNat
        (flatPackedCenterCandidateInsideCost tromino symmetry
          periodicStrip packed base)
        (flatPackedCenterSymmetryListInsideCost tromino
          periodicStrip packed base symmetries)

theorem flatPackedCenterSymmetryListInside
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterSymmetryListInsideCode tromino symmetries)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(symmetries.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat]
      (flatPackedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries) := by
  induction symmetries with
  | nil =>
      simpa [Code.flatPackedCenterSymmetryListInsideCode,
        flatPackedCenterSymmetryListInsideCost] using
        one (Code.flatPackedCenterCandidateInput
          periodicStrip packed base)
  | cons symmetry symmetries induction =>
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      have headFit :
          EvaluatorCodeFits
            (Code.flatPackedCenterCandidateInsideCode tromino symmetry)
            (Code.flatPackedCenterCandidateInput periodicStrip packed base)
            [head.toNat]
            (flatPackedCenterCandidateInsideCost tromino symmetry
              periodicStrip packed base) := by
        simpa [head] using flatPackedCenterCandidateInside
          tromino symmetry periodicStrip wellFormed packed base
      have tailFit :
          EvaluatorCodeFits
            (Code.flatPackedCenterSymmetryListInsideCode
              tromino symmetries)
            (Code.flatPackedCenterCandidateInput periodicStrip packed base)
            [tail.toNat]
            (flatPackedCenterSymmetryListInsideCost tromino
              periodicStrip packed base symmetries) := by
        simpa [tail] using induction
      simpa [Code.flatPackedCenterSymmetryListInsideCode,
        flatPackedCenterSymmetryListInsideCost, head, tail] using
        boolAnd_fit_bool head tail headFit tailFit

theorem flatPackedCenterSymmetryListOneCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    oneCost (Code.flatPackedCenterCandidateInput
        periodicStrip packed base) ≤
      200000 *
        flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  have zeroBound := listCodeZeroCost_le_linear values
  have successorSmall : succCost [0] ≤ 100000 := by
    native_decide
  change oneCost values ≤
    200000 * (encodedListSpace values + 10)
  simp only [oneCost]
  omega

/-- A recursive workspace envelope for a compile-time list of symmetry
candidates.  The exported checker specializes this recurrence to eight
entries. -/
def flatPackedCenterSymmetryListInsideSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List SquareSymmetry → Nat
  | [] =>
      200000 *
        flatPackedCenterCandidateInputUnit periodicStrip packed base
  | symmetry :: symmetries =>
      let budget :=
        flatPackedCenterCandidateInsideSpaceBound tromino symmetry
            periodicStrip packed base +
          flatPackedCenterSymmetryListInsideSpaceBound tromino
            periodicStrip packed base symmetries +
          flatPackedCenterCandidateInputUnit periodicStrip packed base + 100
      1000 * (budget + 1)

set_option maxHeartbeats 800000 in
theorem flatPackedCenterSymmetryListInsideCost_le_linear
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries ≤
      flatPackedCenterSymmetryListInsideSpaceBound tromino
        periodicStrip packed base symmetries := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  induction symmetries with
  | nil =>
      exact flatPackedCenterSymmetryListOneCost_le_linear
        periodicStrip packed base
  | cons symmetry symmetries induction =>
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      let headCost := flatPackedCenterCandidateInsideCost tromino symmetry
        periodicStrip packed base
      let tailCost := flatPackedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries
      let budget :=
        flatPackedCenterCandidateInsideSpaceBound tromino symmetry
            periodicStrip packed base +
          flatPackedCenterSymmetryListInsideSpaceBound tromino
            periodicStrip packed base symmetries +
          flatPackedCenterCandidateInputUnit periodicStrip packed base + 100
      have valuesBound : encodedListSpace values + 1 ≤ budget := by
        simp only [values, budget, flatPackedCenterCandidateInputUnit]
        omega
      have budgetPositive : 1 ≤ budget := by omega
      have headCostBound : headCost ≤ budget := by
        have bound := flatPackedCenterCandidateInsideCost_le_bound
          tromino symmetry periodicStrip packed base
        simp only [headCost, budget]
        omega
      have tailCostBound : tailCost ≤ budget := by
        simp only [tailCost, budget]
        omega
      have headSpace :=
        listCodeEncodedListSpace_singleton_headI_le values
      have headBitsInput :
          (Computability.encodeNat values.headI).length ≤
            encodedListSpace values := by
        simpa [encodedListSpace_cons] using headSpace
      have headBits :
          (Computability.encodeNat values.headI).length ≤ budget := by
        omega
      have successorBits :=
        listCodeEncodeNat_succ_length_le values.headI
      have headSuccessorBits :
          (Computability.encodeNat (values.headI + 1)).length ≤
            budget := by
        rw [← Nat.succ_eq_add_one]
        omega
      have result := boolAndCost_le_budget values head.toNat tail.toNat
        headCost tailCost budget
        (by cases head <;> simp) (by cases tail <;> simp)
        (by omega) headBits headSuccessorBits
        headCostBound tailCostBound budgetPositive
      change boolAndCost values head.toNat tail.toNat
          headCost tailCost ≤ 1000 * (budget + 1)
      exact result

/-- Coefficient obtained by lifting the uniform candidate bound through a
compile-time conjunction list. -/
def flatPackedCenterSymmetryListInsideQuadraticCoefficient :
    List SquareSymmetry → Nat
  | [] => 200000
  | _ :: symmetries =>
      1000 * (flatPackedCenterCandidateInsideQuadraticCoefficient +
        flatPackedCenterSymmetryListInsideQuadraticCoefficient symmetries + 102)

set_option maxRecDepth 100000 in
theorem flatPackedCenterSymmetryListInsideSpaceBound_le_quadratic
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
      flatPackedCenterSymmetryListInsideSpaceBound tromino periodicStrip
        packed base symmetries ≤
      flatPackedCenterSymmetryListInsideQuadraticCoefficient symmetries *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have inputPositive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have inputLarge : 10 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have inputQuadratic : input ≤ input ^ 2 := by nlinarith
  induction symmetries with
  | nil =>
      simp [flatPackedCenterSymmetryListInsideSpaceBound,
        flatPackedCenterSymmetryListInsideQuadraticCoefficient]
      nlinarith
  | cons symmetry symmetries induction =>
      have head := flatPackedCenterCandidateInsideSpaceBound_le_quadratic
        tromino symmetry periodicStrip packed base
      have sumBound :
          flatPackedCenterCandidateInsideSpaceBound tromino symmetry
                periodicStrip packed base +
              flatPackedCenterSymmetryListInsideSpaceBound tromino
                periodicStrip packed base symmetries + input + 100 + 1 ≤
            (flatPackedCenterCandidateInsideQuadraticCoefficient +
              flatPackedCenterSymmetryListInsideQuadraticCoefficient
                symmetries + 102) * input ^ 2 := by
        simp only [input] at head induction ⊢
        calc
          _ ≤ flatPackedCenterCandidateInsideQuadraticCoefficient * input ^ 2 +
                flatPackedCenterSymmetryListInsideQuadraticCoefficient
                  symmetries * input ^ 2 + input + 100 + 1 := by
            dsimp only [input]
            omega
          _ ≤ flatPackedCenterCandidateInsideQuadraticCoefficient * input ^ 2 +
                flatPackedCenterSymmetryListInsideQuadraticCoefficient
                  symmetries * input ^ 2 + input ^ 2 +
                101 * input ^ 2 := by
            nlinarith
          _ = (flatPackedCenterCandidateInsideQuadraticCoefficient +
                flatPackedCenterSymmetryListInsideQuadraticCoefficient
                  symmetries + 102) * input ^ 2 := by ring
      change
        1000 *
            (flatPackedCenterCandidateInsideSpaceBound tromino symmetry
                periodicStrip packed base +
              flatPackedCenterSymmetryListInsideSpaceBound tromino
                periodicStrip packed base symmetries + input + 100 + 1) ≤
          flatPackedCenterSymmetryListInsideQuadraticCoefficient
            (symmetry :: symmetries) * input ^ 2
      calc
        _ ≤ 1000 *
              ((flatPackedCenterCandidateInsideQuadraticCoefficient +
                flatPackedCenterSymmetryListInsideQuadraticCoefficient
                  symmetries + 102) * input ^ 2) :=
          Nat.mul_le_mul_left _ sumBound
        _ = (1000 *
              (flatPackedCenterCandidateInsideQuadraticCoefficient +
                flatPackedCenterSymmetryListInsideQuadraticCoefficient
                  symmetries + 102)) * input ^ 2 :=
          (Nat.mul_assoc _ _ _).symm
        _ = _ := rfl

def flatPackedCenterAllSymmetriesInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterSymmetryListInsideCost tromino periodicStrip
    packed base TrominoAssignment.squareSymmetryList

def flatPackedCenterAllSymmetriesInsideSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterSymmetryListInsideSpaceBound tromino periodicStrip
    packed base TrominoAssignment.squareSymmetryList

def flatPackedCenterAllSymmetriesInsideQuadraticCoefficient : Nat :=
  flatPackedCenterSymmetryListInsideQuadraticCoefficient
    TrominoAssignment.squareSymmetryList

theorem flatPackedCenterAllSymmetriesInsideSpaceBound_le_quadratic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
      flatPackedCenterAllSymmetriesInsideSpaceBound tromino
        periodicStrip packed base ≤
      flatPackedCenterAllSymmetriesInsideQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 :=
  flatPackedCenterSymmetryListInsideSpaceBound_le_quadratic tromino
    TrominoAssignment.squareSymmetryList periodicStrip packed base

theorem flatPackedCenterAllSymmetriesInsideCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterAllSymmetriesInsideCost tromino
        periodicStrip packed base ≤
      flatPackedCenterAllSymmetriesInsideSpaceBound tromino
        periodicStrip packed base :=
  flatPackedCenterSymmetryListInsideCost_le_linear tromino
    TrominoAssignment.squareSymmetryList periodicStrip packed base

/-- Exact fitted execution of the eight-way center-containment conjunction. -/
theorem flatPackedCenterAllSymmetriesInside
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterAllSymmetriesInsideCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(TrominoAssignment.squareSymmetryList.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat]
      (flatPackedCenterAllSymmetriesInsideCost tromino
        periodicStrip packed base) := by
  exact flatPackedCenterSymmetryListInside tromino
    TrominoAssignment.squareSymmetryList periodicStrip
    wellFormed packed base

end EvaluatorCodeFits

end PartrecToTM2
end Turing

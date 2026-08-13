/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPackedCenterCandidateSpace
import LeanTrominoes.PartrecPackedCenterSymmetries

/-!
# Evaluator-space certificate for all packed center symmetries

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
def packedCenterSymmetryListInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List SquareSymmetry -> Nat
  | [] => oneCost
      (Code.packedCenterCandidateInput periodicStrip packed base)
  | symmetry :: symmetries =>
      let values :=
        Code.packedCenterCandidateInput periodicStrip packed base
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      boolAndCost values head.toNat tail.toNat
        (packedCenterCandidateInsideCost tromino symmetry
          periodicStrip packed base)
        (packedCenterSymmetryListInsideCost tromino
          periodicStrip packed base symmetries)

theorem packedCenterSymmetryListInside
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterSymmetryListInsideCode tromino symmetries)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(symmetries.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat]
      (packedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries) := by
  induction symmetries with
  | nil =>
      simpa [Code.packedCenterSymmetryListInsideCode,
        packedCenterSymmetryListInsideCost] using
        one (Code.packedCenterCandidateInput
          periodicStrip packed base)
  | cons symmetry symmetries induction =>
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      have headFit :
          EvaluatorCodeFits
            (Code.packedCenterCandidateInsideCode tromino symmetry)
            (Code.packedCenterCandidateInput periodicStrip packed base)
            [head.toNat]
            (packedCenterCandidateInsideCost tromino symmetry
              periodicStrip packed base) := by
        simpa [head] using packedCenterCandidateInside
          tromino symmetry periodicStrip wellFormed packed base
      have tailFit :
          EvaluatorCodeFits
            (Code.packedCenterSymmetryListInsideCode
              tromino symmetries)
            (Code.packedCenterCandidateInput periodicStrip packed base)
            [tail.toNat]
            (packedCenterSymmetryListInsideCost tromino
              periodicStrip packed base symmetries) := by
        simpa [tail] using induction
      simpa [Code.packedCenterSymmetryListInsideCode,
        packedCenterSymmetryListInsideCost, head, tail] using
        boolAnd_fit_bool head tail headFit tailFit

theorem packedCenterSymmetryListOneCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    oneCost (Code.packedCenterCandidateInput
        periodicStrip packed base) ≤
      200000 *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  have zeroBound := listCodeZeroCost_le_linear values
  have successorSmall : succCost [0] ≤ 100000 := by
    native_decide
  change oneCost values ≤
    200000 * (encodedListSpace values + 1)
  simp only [oneCost]
  omega

/-- A recursive workspace envelope for a compile-time list of symmetry
candidates.  The exported checker specializes this recurrence to eight
entries. -/
def packedCenterSymmetryListInsideSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List SquareSymmetry → Nat
  | [] =>
      200000 *
        packedCenterCandidateInputUnit periodicStrip packed base
  | symmetry :: symmetries =>
      let budget :=
        packedCenterCandidateInsideSpaceBound tromino symmetry
            periodicStrip packed base +
          packedCenterSymmetryListInsideSpaceBound tromino
            periodicStrip packed base symmetries +
          packedCenterCandidateInputUnit periodicStrip packed base + 100
      1000 * (budget + 1)

set_option maxHeartbeats 800000 in
theorem packedCenterSymmetryListInsideCost_le_linear
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries ≤
      packedCenterSymmetryListInsideSpaceBound tromino
        periodicStrip packed base symmetries := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  induction symmetries with
  | nil =>
      exact packedCenterSymmetryListOneCost_le_linear
        periodicStrip packed base
  | cons symmetry symmetries induction =>
      let head := packed.centerSymmetryInsideBool tromino
        periodicStrip base symmetry
      let tail := symmetries.all fun remaining =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base remaining
      let headCost := packedCenterCandidateInsideCost tromino symmetry
        periodicStrip packed base
      let tailCost := packedCenterSymmetryListInsideCost tromino
        periodicStrip packed base symmetries
      let budget :=
        packedCenterCandidateInsideSpaceBound tromino symmetry
            periodicStrip packed base +
          packedCenterSymmetryListInsideSpaceBound tromino
            periodicStrip packed base symmetries +
          packedCenterCandidateInputUnit periodicStrip packed base + 100
      have valuesBound : encodedListSpace values + 1 ≤ budget := by
        simp only [values, budget, packedCenterCandidateInputUnit]
        omega
      have budgetPositive : 1 ≤ budget := by omega
      have headCostBound : headCost ≤ budget := by
        have bound := packedCenterCandidateInsideCost_le_linear
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
def packedCenterSymmetryListInsideLinearCoefficient :
    List SquareSymmetry → Nat
  | [] => 200000
  | _ :: symmetries =>
      1000 * (packedCenterCandidateInsideLinearCoefficient +
        packedCenterSymmetryListInsideLinearCoefficient symmetries + 102)

set_option maxRecDepth 100000 in
theorem packedCenterSymmetryListInsideSpaceBound_le_input
    (tromino : Tromino) (symmetries : List SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterSymmetryListInsideSpaceBound tromino periodicStrip
        packed base symmetries ≤
      packedCenterSymmetryListInsideLinearCoefficient symmetries *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let input := packedCenterCandidateInputUnit periodicStrip packed base
  have inputPositive : 1 ≤ input := by
    simp [input, packedCenterCandidateInputUnit]
  induction symmetries with
  | nil => rfl
  | cons symmetry symmetries induction =>
      have head := packedCenterCandidateInsideSpaceBound_le_input
        tromino symmetry periodicStrip packed base
      have sumBound :
          packedCenterCandidateInsideSpaceBound tromino symmetry
                periodicStrip packed base +
              packedCenterSymmetryListInsideSpaceBound tromino
                periodicStrip packed base symmetries + input + 100 + 1 ≤
            (packedCenterCandidateInsideLinearCoefficient +
              packedCenterSymmetryListInsideLinearCoefficient symmetries +
              102) * input := by
        simp only [input] at head induction ⊢
        calc
          _ ≤ packedCenterCandidateInsideLinearCoefficient * input +
                packedCenterSymmetryListInsideLinearCoefficient symmetries *
                  input + input + 100 + 1 := by
            dsimp only [input]
            omega
          _ = (packedCenterCandidateInsideLinearCoefficient +
                packedCenterSymmetryListInsideLinearCoefficient symmetries +
                1) * input + 101 := by ring
          _ ≤ (packedCenterCandidateInsideLinearCoefficient +
                packedCenterSymmetryListInsideLinearCoefficient symmetries +
                1) * input + 101 * input :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left 101 inputPositive) _
          _ = (packedCenterCandidateInsideLinearCoefficient +
                packedCenterSymmetryListInsideLinearCoefficient symmetries +
                102) * input := by ring
      change
        1000 *
            (packedCenterCandidateInsideSpaceBound tromino symmetry
                periodicStrip packed base +
              packedCenterSymmetryListInsideSpaceBound tromino
                periodicStrip packed base symmetries + input + 100 + 1) ≤
          packedCenterSymmetryListInsideLinearCoefficient
            (symmetry :: symmetries) * input
      calc
        _ ≤ 1000 *
              ((packedCenterCandidateInsideLinearCoefficient +
                packedCenterSymmetryListInsideLinearCoefficient symmetries +
                102) * input) :=
          Nat.mul_le_mul_left _ sumBound
        _ = (1000 *
              (packedCenterCandidateInsideLinearCoefficient +
                packedCenterSymmetryListInsideLinearCoefficient symmetries +
                102)) * input :=
          (Nat.mul_assoc _ _ _).symm
        _ = _ := rfl

def packedCenterAllSymmetriesInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterSymmetryListInsideCost tromino periodicStrip
    packed base TrominoAssignment.squareSymmetryList

def packedCenterAllSymmetriesInsideSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterSymmetryListInsideSpaceBound tromino periodicStrip
    packed base TrominoAssignment.squareSymmetryList

def packedCenterAllSymmetriesInsideLinearCoefficient : Nat :=
  packedCenterSymmetryListInsideLinearCoefficient
    TrominoAssignment.squareSymmetryList

theorem packedCenterAllSymmetriesInsideSpaceBound_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterAllSymmetriesInsideSpaceBound tromino
        periodicStrip packed base ≤
      packedCenterAllSymmetriesInsideLinearCoefficient *
        packedCenterCandidateInputUnit periodicStrip packed base :=
  packedCenterSymmetryListInsideSpaceBound_le_input tromino
    TrominoAssignment.squareSymmetryList periodicStrip packed base

theorem packedCenterAllSymmetriesInsideCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterAllSymmetriesInsideCost tromino
        periodicStrip packed base ≤
      packedCenterAllSymmetriesInsideSpaceBound tromino
        periodicStrip packed base :=
  packedCenterSymmetryListInsideCost_le_linear tromino
    TrominoAssignment.squareSymmetryList periodicStrip packed base

/-- Exact fitted execution of the eight-way center-containment conjunction. -/
theorem packedCenterAllSymmetriesInside
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterAllSymmetriesInsideCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(TrominoAssignment.squareSymmetryList.all fun symmetry =>
        packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry).toNat]
      (packedCenterAllSymmetriesInsideCost tromino
        periodicStrip packed base) := by
  exact packedCenterSymmetryListInside tromino
    TrominoAssignment.squareSymmetryList periodicStrip
    wellFormed packed base

end EvaluatorCodeFits

end PartrecToTM2
end Turing

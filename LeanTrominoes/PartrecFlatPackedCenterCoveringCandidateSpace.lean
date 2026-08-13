/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedCenterCoveringCandidate
import LeanTrominoes.PartrecFlatPackedCenterCandidateSpace

/-!
# Evaluator-space certificate for flat packed center-covering candidates

The candidate program reuses the canonical packed target constructor and the
fitted fixed-assignment predicate.  This file records the exact composition
cost and its semantic fitted execution.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def flatPackedCenterCoveringAssignmentArgumentsCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedTargetMembershipLookupArgumentsCost
      (Code.packedCoveringColumn symmetry source)
      (-(symmetry.act source).2)
      periodicStrip.period packed.phase periodicStrip.motif
      base.2 packed.assignmentWord +
    flatPackedCenterSourceInputCost periodicStrip packed base

theorem flatPackedCenterCoveringAssignmentArguments
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCoveringAssignmentArgumentsCode
        symmetry source)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      ([periodicStrip.motif.length,
          (Code.packedCoveringColumn symmetry source).val,
          Encodable.encode (Code.packedCenterCoveringTarget
            periodicStrip packed base symmetry source).1,
          Encodable.encode (Code.packedCenterCoveringTarget
            periodicStrip packed base symmetry source).2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields)
      (flatPackedCenterCoveringAssignmentArgumentsCost
        symmetry source periodicStrip packed base) := by
  have target := flatPackedTargetMembershipLookupArguments
    (Code.packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)
    periodicStrip.period packed.phase periodicStrip.motif
    base.2 packed.assignmentWord
  have result :=
    comp target (flatPackedCenterSourceInput periodicStrip packed base)
  let x := Code.packedColumnPhaseNumerator periodicStrip.period
    packed.phase (Code.packedCoveringColumn symmetry source).val %
      periodicStrip.period
  have targetEq :
      ((Int.ofNat x,
        base.2 + -(symmetry.act source).2) : Cell) =
        Code.packedCenterCoveringTarget
          periodicStrip packed base symmetry source := by
    apply Prod.ext
    · simp only [Code.packedCenterCoveringTarget,
        PackedWindowState.columnPhase, x,
        Code.packedColumnPhaseNumerator,
        Code.packedColumnPhaseSum]
      congr 2
      omega
    · simp only [Code.packedCenterCoveringTarget]
      omega
  rw [targetEq] at result
  have encodedX : Encodable.encode
      (Code.packedCenterCoveringTarget periodicStrip packed base symmetry
        source).1 = 2 * x := by
    rw [← targetEq]
    rfl
  rw [encodedX]
  simpa [Code.flatPackedCenterCoveringAssignmentArgumentsCode,
    flatPackedCenterCoveringAssignmentArgumentsCost] using result

theorem flatPackedCenterCoveringTarget_eq_targetMembership
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source =
      (Int.ofNat
          (Code.packedColumnPhaseNumerator periodicStrip.period
            packed.phase (Code.packedCoveringColumn symmetry source).val %
            periodicStrip.period),
        base.2 + -(symmetry.act source).2) := by
  apply Prod.ext
  · simp only [Code.packedCenterCoveringTarget,
      PackedWindowState.columnPhase,
      Code.packedColumnPhaseNumerator, Code.packedColumnPhaseSum]
    congr 2
    omega
  · simp only [Code.packedCenterCoveringTarget]
    omega

def flatPackedCenterCoveringCandidateCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedAssignmentIsCost (some symmetry) periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord +
    flatPackedCenterCoveringAssignmentArgumentsCost
      symmetry source periodicStrip packed base

def flatPackedCenterCoveringCandidateSpaceBound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedAssignmentPredicateSpaceBound periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord +
    flatPackedCenterCoveringAssignmentArgumentsCost
      symmetry source periodicStrip packed base

theorem flatPackedCenterCoveringCandidateCost_le_bound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCoveringCandidateCost symmetry source
        periodicStrip packed base ≤
      flatPackedCenterCoveringCandidateSpaceBound symmetry source
        periodicStrip packed base := by
  exact Nat.add_le_add_right
    (flatPackedAssignmentIsCost_le_bound (some symmetry)
      periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord)
    _

/-! ## Native quadratic bound -/

/-- A uniform linear allowance for constructing any center-covering target
whose compile-time vertical offset has magnitude at most four. -/
def flatPackedCenterCoveringConstructorLinearCoefficient : Nat := 10 ^ 62

/-- A deliberately coarse uniform coefficient for a center-covering
candidate.  The candidate list is compile-time data, so this coefficient is
independent of the input motif. -/
def flatPackedCenterCoveringCandidateQuadraticCoefficient : Nat := 10 ^ 500

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem flatPackedCenterCoveringCandidateSpaceBound_le_quadratic
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall : intOffsetAmount (-(symmetry.act source).2) ≤ 4) :
    flatPackedCenterCoveringCandidateSpaceBound symmetry source
        periodicStrip packed base ≤
      flatPackedCenterCoveringCandidateQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let column := Code.packedCoveringColumn symmetry source
  let offset := -(symmetry.act source).2
  let unit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  let native := flatPackedTargetMembershipNativeInputSpace column offset
    periodicStrip.period packed.phase periodicStrip.motif base.2
    packed.assignmentWord
  let constructorBudget := flatPackedTargetConstructorBudget column offset
    periodicStrip.period packed.phase periodicStrip.motif base.2
    packed.assignmentWord
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have amountBound : intOffsetAmount offset + 1 ≤ 5 := by
    simp only [offset]
    omega
  have nativeBound : native ≤ 2 * unit := by
    simpa [native, column, offset, unit] using
      flatPackedCenterTargetNativeInput_le_candidate column offset
        periodicStrip packed base (by simpa [offset] using offsetSmall)
  have constructorCoefficientBound :
      10 *
          1000000000000000000000000000000000000000000000000000000000000 ≤
        flatPackedCenterCoveringConstructorLinearCoefficient := by
    native_decide
  have constructorBound : constructorBudget ≤
      flatPackedCenterCoveringConstructorLinearCoefficient * unit := by
    calc
      constructorBudget =
          1000000000000000000000000000000000000000000000000000000000000 *
            (intOffsetAmount offset + 1) * native := by
        rfl
      _ ≤ 1000000000000000000000000000000000000000000000000000000000000 *
            5 * (2 * unit) := by gcongr
      _ = (10 *
          1000000000000000000000000000000000000000000000000000000000000) *
            unit := by ring
      _ ≤ flatPackedCenterCoveringConstructorLinearCoefficient * unit :=
        Nat.mul_le_mul_right unit constructorCoefficientBound
  have assignmentNative :
      flatPackedAssignmentLookupNativeInputSpace periodicStrip.motif column.val
          (Code.packedCenterCoveringTarget periodicStrip packed base
            symmetry source) packed.assignmentWord ≤
        3 * constructorBudget := by
    have raw := flatPackedTargetAssignmentInputSpace_le_constructor column
      offset periodicStrip.period packed.phase periodicStrip.motif base.2
      packed.assignmentWord
    simp only at raw
    rw [← flatPackedCenterCoveringTarget_eq_targetMembership symmetry source
      periodicStrip packed base] at raw
    simpa [column, offset, constructorBudget] using raw
  have predicate :=
    flatPackedAssignmentPredicateSpaceBound_le_native_quadratic
      periodicStrip.motif column.val
      (Code.packedCenterCoveringTarget periodicStrip packed base
        symmetry source) packed.assignmentWord
  have predicateGlobal :
      flatPackedAssignmentPredicateSpaceBound periodicStrip.motif column.val
          (Code.packedCenterCoveringTarget periodicStrip packed base
            symmetry source) packed.assignmentWord ≤
        (10000000000000000000000000000000000000000000000000000000000 *
          (3 * flatPackedCenterCoveringConstructorLinearCoefficient) ^ 2) *
            unit ^ 2 := by
    calc
      _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
          (flatPackedAssignmentLookupNativeInputSpace periodicStrip.motif
            column.val
            (Code.packedCenterCoveringTarget periodicStrip packed base
              symmetry source) packed.assignmentWord) ^ 2 := predicate
      _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
          (3 * constructorBudget) ^ 2 := by gcongr
      _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
          (3 * (flatPackedCenterCoveringConstructorLinearCoefficient *
            unit)) ^ 2 := by gcongr
      _ = (10000000000000000000000000000000000000000000000000000000000 *
          (3 * flatPackedCenterCoveringConstructorLinearCoefficient) ^ 2) *
            unit ^ 2 := by ring
  have lookupArguments :=
    flatPackedTargetMembershipLookupArgumentsCost_le_constructor column offset
      periodicStrip.period packed.phase periodicStrip.motif base.2
      packed.assignmentWord
  have sourceArguments := flatPackedCenterSourceInputCost_le_linear
    periodicStrip packed base
  have argumentsGlobal :
      flatPackedCenterCoveringAssignmentArgumentsCost symmetry source
          periodicStrip packed base ≤
        (100 * flatPackedCenterCoveringConstructorLinearCoefficient +
          1000000000) * unit ^ 2 := by
    simp only [flatPackedCenterCoveringAssignmentArgumentsCost,
      column, offset] at lookupArguments ⊢
    calc
      _ ≤ 100 * constructorBudget + 1000000000 * unit :=
        Nat.add_le_add lookupArguments sourceArguments
      _ ≤ (100 * flatPackedCenterCoveringConstructorLinearCoefficient +
            1000000000) * unit := by
        calc
          _ ≤ 100 *
                (flatPackedCenterCoveringConstructorLinearCoefficient * unit) +
              1000000000 * unit := by gcongr
          _ = (100 * flatPackedCenterCoveringConstructorLinearCoefficient +
                1000000000) * unit := by ring
      _ ≤ (100 * flatPackedCenterCoveringConstructorLinearCoefficient +
            1000000000) * unit ^ 2 :=
        Nat.mul_le_mul_left _ unitQuadratic
  have coefficientBound :
      10000000000000000000000000000000000000000000000000000000000 *
            (3 * flatPackedCenterCoveringConstructorLinearCoefficient) ^ 2 +
          (100 * flatPackedCenterCoveringConstructorLinearCoefficient +
            1000000000) ≤
        flatPackedCenterCoveringCandidateQuadraticCoefficient := by
    native_decide
  change flatPackedAssignmentPredicateSpaceBound periodicStrip.motif
        column.val
        (Code.packedCenterCoveringTarget periodicStrip packed base
          symmetry source) packed.assignmentWord +
      flatPackedCenterCoveringAssignmentArgumentsCost symmetry source
        periodicStrip packed base ≤
    flatPackedCenterCoveringCandidateQuadraticCoefficient * unit ^ 2
  calc
    _ ≤ (10000000000000000000000000000000000000000000000000000000000 *
            (3 * flatPackedCenterCoveringConstructorLinearCoefficient) ^ 2 +
          (100 * flatPackedCenterCoveringConstructorLinearCoefficient +
            1000000000)) * unit ^ 2 := by
      nlinarith
    _ ≤ flatPackedCenterCoveringCandidateQuadraticCoefficient * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficientBound

/-- Exact fitted execution of one active covering-placement test. -/
theorem flatPackedCenterCoveringCandidate
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCoveringCandidateCode symmetry source)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2) (symmetry.act source)) =
            some symmetry)).toNat]
      (flatPackedCenterCoveringCandidateCost symmetry source
        periodicStrip packed base) := by
  have selected := flatPackedAssignmentIs_semantic
    (some symmetry) periodicStrip packed
    (Code.packedCoveringColumn symmetry source)
    (Code.packedCenterCoveringTarget
      periodicStrip packed base symmetry source)
  have result := comp selected
    (flatPackedCenterCoveringAssignmentArguments
      symmetry source periodicStrip packed base)
  rw [Code.packedCenterCoveringAssignment_eq_local
    tromino symmetry source sourceMember periodicStrip packed base] at result
  simpa [Code.flatPackedCenterCoveringCandidateCode,
    flatPackedCenterCoveringCandidateCost] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing

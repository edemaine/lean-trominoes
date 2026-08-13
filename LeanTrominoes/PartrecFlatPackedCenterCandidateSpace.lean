/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecFlatPackedCenterCandidate
import LeanTrominoes.PartrecFlatPackedTargetMembershipSpace

/-!
# Evaluator-space certificates for flat packed center-candidate leaves

This file fits the two native adapters shared by center candidates and the
assignment-selection and translated target-membership leaves built on them.
The motif remains a flat coordinate suffix throughout.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedCenterCandidateInputUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  encodedListSpace
      (Code.flatPackedCenterCandidateInput periodicStrip packed base) + 10

def flatPackedCenterAssignmentArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let restWord := prependCost values [packed.assignmentWord]
    (periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 5 values) (dropCost 6 values)
  let restY := prependCost values [Encodable.encode base.2]
    (packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 4 values) restWord
  let restX := prependCost values [Encodable.encode base.1]
    (Encodable.encode base.2 :: packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 3 values) restY
  let restColumn := prependCost values [WindowState.center.val]
    (Encodable.encode base.1 :: Encodable.encode base.2 ::
      packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (numeralCost WindowState.center.val values) restX
  prependCost values [periodicStrip.motif.length]
    (WindowState.center.val :: Encodable.encode base.1 ::
      Encodable.encode base.2 :: packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 2 values) restColumn

theorem flatPackedCenterAssignmentArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.flatPackedCenterAssignmentArgumentsCode
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      ([periodicStrip.motif.length, WindowState.center.val,
          Encodable.encode base.1, Encodable.encode base.2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields)
      (flatPackedCenterAssignmentArgumentsCost
        periodicStrip packed base) := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  have restWord := prepend (get 5 values) (drop 6 values)
  have restY := prepend (get 4 values) restWord
  have restX := prepend (get 3 values) restY
  have restColumn := prepend
    (numeral WindowState.center.val values) restX
  have result := prepend (get 2 values) restColumn
  simpa [Code.flatPackedCenterAssignmentArgumentsCode,
    flatPackedCenterAssignmentArgumentsCost,
    Code.flatPackedCenterCandidateInput,
    prependCost, values] using result

theorem flatPackedCenterAssignmentArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterAssignmentArgumentsCost periodicStrip packed base ≤
      1000000000 *
        flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let unit := encodedListSpace values + 10
  have get2 := listCodeGetCost_le_linear 2 values
  have get3 := listCodeGetCost_le_linear 3 values
  have get4 := listCodeGetCost_le_linear 4 values
  have get5 := listCodeGetCost_le_linear 5 values
  have drop6 := flatLookupDropCost_le_linear 6 values
  have zeroBound := listCodeZeroCost_le_linear values
  have addSmall : addConstCost WindowState.center.val [0] ≤ 100000 := by
    native_decide
  have centerBits :
      (Computability.encodeNat WindowState.center.val).length ≤ 100 := by
    native_decide
  have numeralBound : numeralCost WindowState.center.val values ≤
      1000000 * unit := by
    simp only [numeralCost]
    omega
  change flatPackedCenterAssignmentArgumentsCost periodicStrip packed base ≤
    1000000000 * unit
  dsimp only [unit] at *
  simp [flatPackedCenterAssignmentArgumentsCost, prependCost,
    values, Code.flatPackedCenterCandidateInput,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

def flatPackedCenterAssignmentIsCost
    (_symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedAssignmentPredicateSpaceBound periodicStrip.motif
      WindowState.center.val base packed.assignmentWord +
    flatPackedCenterAssignmentArgumentsCost periodicStrip packed base

theorem flatPackedCenterAssignmentIs
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    let selected := decide
      (packed.assignmentAtCell periodicStrip
        WindowState.center base = some symmetry)
    EvaluatorCodeFits
      (Code.flatPackedCenterAssignmentIsCode symmetry)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [selected.toNat]
      (flatPackedCenterAssignmentIsCost
        symmetry periodicStrip packed base) := by
  simp only
  have selected := (flatPackedAssignmentIs_semantic (some symmetry)
    periodicStrip packed WindowState.center base).mono
      (flatPackedAssignmentIsCost_le_bound (some symmetry)
        periodicStrip.motif WindowState.center.val base
        packed.assignmentWord)
  simpa [Code.flatPackedCenterAssignmentIsCode,
    flatPackedCenterAssignmentIsCost] using
    comp selected
      (flatPackedCenterAssignmentArguments periodicStrip packed base)

def flatPackedCenterSourceInputCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let restWord := prependCost values [packed.assignmentWord]
    (periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 5 values) (dropCost 6 values)
  let restY := prependCost values [Encodable.encode base.2]
    (packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 4 values) restWord
  let restMotif := prependCost values [periodicStrip.motif.length]
    (Encodable.encode base.2 :: packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 2 values) restY
  let restPhase := prependCost values [packed.phase]
    (periodicStrip.motif.length :: Encodable.encode base.2 ::
      packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 1 values) restMotif
  prependCost values [periodicStrip.period]
    (packed.phase :: periodicStrip.motif.length ::
      Encodable.encode base.2 :: packed.assignmentWord ::
      periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
    (getCost 0 values) restPhase

theorem flatPackedCenterSourceInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.flatPackedCenterSourceInputCode
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      ([periodicStrip.period, packed.phase,
          periodicStrip.motif.length, Encodable.encode base.2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields)
      (flatPackedCenterSourceInputCost periodicStrip packed base) := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  have restWord := prepend (get 5 values) (drop 6 values)
  have restY := prepend (get 4 values) restWord
  have restMotif := prepend (get 2 values) restY
  have restPhase := prepend (get 1 values) restMotif
  have result := prepend (get 0 values) restPhase
  simpa [Code.flatPackedCenterSourceInputCode,
    flatPackedCenterSourceInputCost,
    Code.flatPackedCenterCandidateInput,
    prependCost, values] using result

theorem flatPackedCenterSourceInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterSourceInputCost periodicStrip packed base ≤
      1000000000 *
        flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let unit := encodedListSpace values + 10
  have get0 := listCodeGetCost_le_linear 0 values
  have get1 := listCodeGetCost_le_linear 1 values
  have get2 := listCodeGetCost_le_linear 2 values
  have get4 := listCodeGetCost_le_linear 4 values
  have get5 := listCodeGetCost_le_linear 5 values
  have drop6 := flatLookupDropCost_le_linear 6 values
  change flatPackedCenterSourceInputCost periodicStrip packed base ≤
    1000000000 * unit
  dsimp only [unit] at *
  simp [flatPackedCenterSourceInputCost, prependCost,
    values, Code.flatPackedCenterCandidateInput,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

theorem flatPackedCenterAssignmentNativeInput_le_candidate
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedAssignmentLookupNativeInputSpace periodicStrip.motif
        WindowState.center.val base packed.assignmentWord ≤
      2 * flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  have centerBits :
      (Computability.encodeNat WindowState.center.val).length = 2 := by
    native_decide
  simp [flatPackedAssignmentLookupNativeInputSpace,
    flatPackedCenterCandidateInputUnit,
    Code.flatPackedCenterCandidateInput,
    encodedListSpace_cons, centerBits]
  omega

theorem flatPackedCenterTargetNativeInput_le_candidate
    (column : WindowColumn) (verticalOffset : Int)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall : intOffsetAmount verticalOffset ≤ 4) :
    flatPackedTargetMembershipNativeInputSpace column verticalOffset
        periodicStrip.period packed.phase periodicStrip.motif base.2
        packed.assignmentWord ≤
      2 * flatPackedCenterCandidateInputUnit periodicStrip packed base := by
  have columnSmall : column.val ≤ 4 := Nat.le_pred_of_lt column.isLt
  have columnBits := listCodeEncodeNat_length_mono columnSmall
  have offsetBits := listCodeEncodeNat_length_mono offsetSmall
  have fourBits : (Computability.encodeNat 4).length = 3 := by
    native_decide
  rw [fourBits] at columnBits offsetBits
  change
    encodedListSpace
        ([periodicStrip.period, packed.phase, periodicStrip.motif.length,
            Encodable.encode base.2, packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) +
        encodedListSpace [column.val] +
        encodedListSpace [intOffsetAmount verticalOffset] + 10 ≤
      2 * (encodedListSpace
        (Code.flatPackedCenterCandidateInput periodicStrip packed base) + 10)
  simp [Code.flatPackedCenterCandidateInput,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

def flatPackedCenterSourceInsideCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedTargetMembershipSpaceBound
      (Code.packedSourceColumn symmetry source)
      (symmetry.act source).2
      periodicStrip.period packed.phase periodicStrip.motif
      base.2 packed.assignmentWord +
    flatPackedCenterSourceInputCost periodicStrip packed base

theorem flatPackedCenterSourceInside
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterSourceInsideCode symmetry source)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.centerSourceInsideBool periodicStrip
        base symmetry source).toNat]
      (flatPackedCenterSourceInsideCost symmetry source
        periodicStrip packed base) := by
  have horizontal :
      (symmetry.act source).1 =
        (Code.packedSourceColumn symmetry source).displacement :=
    (Code.packedSourceColumn_displacement
      tromino symmetry source sourceMember).symm
  have membership := flatPackedTargetMembershipBounded
    (Code.packedSourceColumn symmetry source)
    (symmetry.act source).2 periodicStrip.period packed.phase
    periodicStrip.motif base.2 packed.assignmentWord
  let x := Code.packedColumnPhaseNumerator periodicStrip.period packed.phase
    (Code.packedSourceColumn symmetry source).val % periodicStrip.period
  let target : Cell := (Int.ofNat x, base.2 + (symmetry.act source).2)
  let outcome := Code.packedAssignmentLookupOutcome periodicStrip.motif
    (Code.packedSourceColumn symmetry source).val target packed.assignmentWord
  have rawRun := Code.flatPackedTargetMembershipCode_eval
    (Code.packedSourceColumn symmetry source) (symmetry.act source).2
    periodicStrip.period packed.phase periodicStrip.motif
    packed.assignmentWord base.2
  have semanticRun :=
    Code.flatPackedTargetMembershipCode_eval_centerSourceInside
      periodicStrip wellFormed packed base symmetry source
      (Code.packedSourceColumn symmetry source) horizontal
  have outputEq : [outcome.2.2.toNat] =
      [(packed.centerSourceInsideBool periodicStrip
        base symmetry source).toNat] := by
    have both := rawRun.symm.trans semanticRun
    simpa [x, target, outcome] using both
  have membershipSemantic :
      EvaluatorCodeFits
        (Code.flatPackedTargetMembershipCode
          (Code.packedSourceColumn symmetry source)
          (symmetry.act source).2)
        ([periodicStrip.period, packed.phase,
            periodicStrip.motif.length, Encodable.encode base.2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields)
        [(packed.centerSourceInsideBool periodicStrip
          base symmetry source).toNat]
        (flatPackedTargetMembershipSpaceBound
          (Code.packedSourceColumn symmetry source)
          (symmetry.act source).2 periodicStrip.period packed.phase
          periodicStrip.motif base.2 packed.assignmentWord) := by
    change EvaluatorCodeFits
      (Code.flatPackedTargetMembershipCode
        (Code.packedSourceColumn symmetry source)
        (symmetry.act source).2)
      ([periodicStrip.period, packed.phase,
          periodicStrip.motif.length, Encodable.encode base.2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [outcome.2.2.toNat]
      (flatPackedTargetMembershipSpaceBound
        (Code.packedSourceColumn symmetry source)
        (symmetry.act source).2 periodicStrip.period packed.phase
        periodicStrip.motif base.2 packed.assignmentWord) at membership
    rw [outputEq] at membership
    exact membership
  simpa [Code.flatPackedCenterSourceInsideCode,
    flatPackedCenterSourceInsideCost] using
    comp membershipSemantic
      (flatPackedCenterSourceInput periodicStrip packed base)

private def flatPackedBoolAndThreeCost
    (values : List Nat)
    (first second third : Bool)
    (firstCost secondCost thirdCost : Nat) : Nat :=
  let tailCost := boolAndCost values
    second.toNat third.toNat secondCost thirdCost
  boolAndCost values first.toNat (second && third).toNat
    firstCost tailCost

private theorem flatPackedBoolAndThree
    (firstCode secondCode thirdCode : Code)
    (values : List Nat)
    (first second third : Bool)
    (firstCost secondCost thirdCost : Nat)
    (firstFit : EvaluatorCodeFits firstCode values
      [first.toNat] firstCost)
    (secondFit : EvaluatorCodeFits secondCode values
      [second.toNat] secondCost)
    (thirdFit : EvaluatorCodeFits thirdCode values
      [third.toNat] thirdCost) :
    EvaluatorCodeFits
      (Code.boolAnd firstCode
        (Code.boolAnd secondCode thirdCode))
      values [(first && (second && third)).toNat]
      (flatPackedBoolAndThreeCost values first second third
        firstCost secondCost thirdCost) := by
  have tailRaw := boolAnd secondFit thirdFit
  have tailFit :
      EvaluatorCodeFits (Code.boolAnd secondCode thirdCode)
        values [(second && third).toNat]
        (boolAndCost values second.toNat third.toNat
          secondCost thirdCost) := by
    cases second <;> cases third <;> simpa using tailRaw
  have resultRaw := boolAnd firstFit tailFit
  cases first <;> cases second <;> cases third <;>
    simpa [flatPackedBoolAndThreeCost] using resultRaw

private theorem flatPackedBoolAndThreeCost_le_budget
    (values : List Nat)
    (first second third : Bool)
    (firstCost secondCost thirdCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (firstCostBound : firstCost ≤ budget)
    (secondCostBound : secondCost ≤ budget)
    (thirdCostBound : thirdCost ≤ budget) :
    flatPackedBoolAndThreeCost values first second third
        firstCost secondCost thirdCost ≤
      2000000 * (budget + 1) := by
  have budgetPositive : 1 ≤ budget := by omega
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have headBits :
      (Computability.encodeNat values.headI).length ≤ budget := by omega
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  have headSuccessorBits :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    rw [← Nat.succ_eq_add_one]
    omega
  have firstSmall : first.toNat ≤ 1 := by cases first <;> simp
  have secondSmall : second.toNat ≤ 1 := by cases second <;> simp
  have thirdSmall : third.toNat ≤ 1 := by cases third <;> simp
  have tail := boolAndCost_le_budget values
    second.toNat third.toNat secondCost thirdCost budget
    secondSmall thirdSmall (by omega) headBits headSuccessorBits
    secondCostBound thirdCostBound budgetPositive
  let outerBudget := 1000 * (budget + 1)
  have outerPositive : 1 ≤ outerBudget := by
    simp [outerBudget]
    omega
  have inputOuter : encodedListSpace values ≤ outerBudget := by
    simp [outerBudget]
    omega
  have headOuter :
      (Computability.encodeNat values.headI).length ≤ outerBudget :=
    headBits.trans (by simp [outerBudget]; omega)
  have headSuccessorOuter :
      (Computability.encodeNat (values.headI + 1)).length ≤ outerBudget :=
    headSuccessorBits.trans (by simp [outerBudget]; omega)
  have firstOuter : firstCost ≤ outerBudget :=
    firstCostBound.trans (by simp [outerBudget]; omega)
  have tailOuter :
      boolAndCost values second.toNat third.toNat
          secondCost thirdCost ≤ outerBudget := by
    simpa [outerBudget] using tail
  have outer := boolAndCost_le_budget values
    first.toNat (second && third).toNat firstCost
    (boolAndCost values second.toNat third.toNat secondCost thirdCost)
    outerBudget firstSmall
    (by cases second <;> cases third <;> simp)
    inputOuter headOuter headSuccessorOuter firstOuter tailOuter outerPositive
  simp only [flatPackedBoolAndThreeCost]
  exact outer.trans (by simp [outerBudget]; omega)

def flatPackedCenterAllSourcesInsideCost
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  match tromino with
  | .I =>
      flatPackedBoolAndThreeCost values
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (0, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (1, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (2, 0))
        (flatPackedCenterSourceInsideCost symmetry (0, 0)
          periodicStrip packed base)
        (flatPackedCenterSourceInsideCost symmetry (1, 0)
          periodicStrip packed base)
        (flatPackedCenterSourceInsideCost symmetry (2, 0)
          periodicStrip packed base)
  | .L =>
      flatPackedBoolAndThreeCost values
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (0, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (1, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (0, 1))
        (flatPackedCenterSourceInsideCost symmetry (0, 0)
          periodicStrip packed base)
        (flatPackedCenterSourceInsideCost symmetry (1, 0)
          periodicStrip packed base)
        (flatPackedCenterSourceInsideCost symmetry (0, 1)
          periodicStrip packed base)

def flatPackedCenterAllSourcesInsideSpaceUnit
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let inputUnit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  match tromino with
  | .I =>
      flatPackedCenterSourceInsideCost symmetry (0, 0)
          periodicStrip packed base +
        flatPackedCenterSourceInsideCost symmetry (1, 0)
          periodicStrip packed base +
        flatPackedCenterSourceInsideCost symmetry (2, 0)
          periodicStrip packed base + inputUnit + 100
  | .L =>
      flatPackedCenterSourceInsideCost symmetry (0, 0)
          periodicStrip packed base +
        flatPackedCenterSourceInsideCost symmetry (1, 0)
          periodicStrip packed base +
        flatPackedCenterSourceInsideCost symmetry (0, 1)
          periodicStrip packed base + inputUnit + 100

def flatPackedCenterAllSourcesInsideSpaceBound
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  2000000 *
    (flatPackedCenterAllSourcesInsideSpaceUnit tromino symmetry
      periodicStrip packed base + 1)

theorem flatPackedCenterAllSourcesInsideCost_le_bound
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterAllSourcesInsideCost tromino symmetry
        periodicStrip packed base ≤
      flatPackedCenterAllSourcesInsideSpaceBound tromino symmetry
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  cases tromino with
  | I =>
      apply flatPackedBoolAndThreeCost_le_budget
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit,
          flatPackedCenterCandidateInputUnit]
        omega
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit]
        omega
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit]
        omega
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit]
        omega
  | L =>
      apply flatPackedBoolAndThreeCost_le_budget
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit,
          flatPackedCenterCandidateInputUnit]
        omega
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit]
        omega
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit]
        omega
      · simp [flatPackedCenterAllSourcesInsideSpaceUnit]
        omega

theorem flatPackedCenterAllSourcesInside
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    let inside :=
      (TrominoAssignment.trominoCellList tromino).all fun source =>
        packed.centerSourceInsideBool periodicStrip base symmetry source
    EvaluatorCodeFits
      (Code.flatPackedCenterAllSourcesInsideCode tromino symmetry)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [inside.toNat]
      (flatPackedCenterAllSourcesInsideCost tromino symmetry
        periodicStrip packed base) := by
  simp only
  cases tromino with
  | I =>
      simpa [Code.flatPackedCenterAllSourcesInsideCode,
        flatPackedCenterAllSourcesInsideCost,
        TrominoAssignment.trominoCellList] using
        flatPackedBoolAndThree
          (Code.flatPackedCenterSourceInsideCode symmetry (0, 0))
          (Code.flatPackedCenterSourceInsideCode symmetry (1, 0))
          (Code.flatPackedCenterSourceInsideCode symmetry (2, 0))
          (Code.flatPackedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (2, 0))
          (flatPackedCenterSourceInsideCost symmetry (0, 0)
            periodicStrip packed base)
          (flatPackedCenterSourceInsideCost symmetry (1, 0)
            periodicStrip packed base)
          (flatPackedCenterSourceInsideCost symmetry (2, 0)
            periodicStrip packed base)
          (flatPackedCenterSourceInside .I symmetry (0, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInside .I symmetry (1, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInside .I symmetry (2, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
  | L =>
      simpa [Code.flatPackedCenterAllSourcesInsideCode,
        flatPackedCenterAllSourcesInsideCost,
        TrominoAssignment.trominoCellList] using
        flatPackedBoolAndThree
          (Code.flatPackedCenterSourceInsideCode symmetry (0, 0))
          (Code.flatPackedCenterSourceInsideCode symmetry (1, 0))
          (Code.flatPackedCenterSourceInsideCode symmetry (0, 1))
          (Code.flatPackedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 1))
          (flatPackedCenterSourceInsideCost symmetry (0, 0)
            periodicStrip packed base)
          (flatPackedCenterSourceInsideCost symmetry (1, 0)
            periodicStrip packed base)
          (flatPackedCenterSourceInsideCost symmetry (0, 1)
            periodicStrip packed base)
          (flatPackedCenterSourceInside .L symmetry (0, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInside .L symmetry (1, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInside .L symmetry (0, 1)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)

def flatPackedCenterCandidateInsideCost
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  let selectedCost := flatPackedCenterAssignmentIsCost symmetry
    periodicStrip packed base
  let absentCost := isZeroCost values selected.toNat selectedCost
  boolOrCost values (!selected).toNat inside.toNat absentCost
    (flatPackedCenterAllSourcesInsideCost tromino symmetry
      periodicStrip packed base)

def flatPackedCenterCandidateInsideSpaceUnit
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterAssignmentIsCost symmetry periodicStrip packed base +
    flatPackedCenterAllSourcesInsideSpaceBound tromino symmetry
      periodicStrip packed base +
    flatPackedCenterCandidateInputUnit periodicStrip packed base + 100

def flatPackedCenterCandidateInsideSpaceBound
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  2000000 *
    (flatPackedCenterCandidateInsideSpaceUnit tromino symmetry
      periodicStrip packed base + 1)

set_option maxHeartbeats 800000 in
theorem flatPackedCenterCandidateInsideCost_le_bound
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCandidateInsideCost tromino symmetry
        periodicStrip packed base ≤
      flatPackedCenterCandidateInsideSpaceBound tromino symmetry
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  let selectedCost := flatPackedCenterAssignmentIsCost symmetry
    periodicStrip packed base
  let insideCost := flatPackedCenterAllSourcesInsideCost tromino symmetry
    periodicStrip packed base
  let budget := flatPackedCenterCandidateInsideSpaceUnit tromino symmetry
    periodicStrip packed base
  have valuesBound : encodedListSpace values + 1 ≤ budget := by
    simp [budget, flatPackedCenterCandidateInsideSpaceUnit,
      flatPackedCenterCandidateInputUnit, values]
    omega
  have selectedCostBound : selectedCost ≤ budget := by
    simp [selectedCost, budget, flatPackedCenterCandidateInsideSpaceUnit]
    omega
  have budgetLarge : 100 ≤ budget := by
    simp [budget, flatPackedCenterCandidateInsideSpaceUnit]
  have insideCostBound : insideCost ≤ budget := by
    have bound := flatPackedCenterAllSourcesInsideCost_le_bound
      tromino symmetry periodicStrip packed base
    simp [insideCost, budget, flatPackedCenterCandidateInsideSpaceUnit]
    omega
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have headBits :
      (Computability.encodeNat values.headI).length ≤ budget := by omega
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  have headSuccessorBits :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    rw [← Nat.succ_eq_add_one]
    omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have selectedSpace : encodedListSpace [selected.toNat] ≤ budget := by
    cases selected <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  have selectedPredSpace :
      encodedListSpace [selected.toNat.pred] ≤ budget := by
    cases selected <;>
      simp [encodedListSpace_cons, encodedListSpace_nil, zeroBits] <;> omega
  have absentCostBound := isZeroCost_le_budget values selected.toNat
    selectedCost budget (by omega) selectedSpace selectedPredSpace
    headBits headSuccessorBits selectedCostBound (by omega)
  let outerBudget := 1000 * (budget + 1)
  have valuesOuter : encodedListSpace values ≤ outerBudget := by
    simp [outerBudget]
    omega
  have headOuter :
      (Computability.encodeNat values.headI).length ≤ outerBudget :=
    headBits.trans (by simp [outerBudget]; omega)
  have headSuccessorOuter :
      (Computability.encodeNat (values.headI + 1)).length ≤ outerBudget :=
    headSuccessorBits.trans (by simp [outerBudget]; omega)
  have absentOuter :
      isZeroCost values selected.toNat selectedCost ≤ outerBudget := by
    simpa [outerBudget] using absentCostBound
  have insideOuter : insideCost ≤ outerBudget :=
    insideCostBound.trans (by simp [outerBudget]; omega)
  have result := boolOrCost_le_budget values
    (!selected).toNat inside.toNat
    (isZeroCost values selected.toNat selectedCost) insideCost
    outerBudget (by cases selected <;> simp)
    (by cases inside <;> simp) valuesOuter headOuter headSuccessorOuter
    absentOuter insideOuter (by simp [outerBudget]; omega)
  change boolOrCost values (!selected).toNat inside.toNat
      (isZeroCost values selected.toNat selectedCost) insideCost ≤
    2000000 * (budget + 1)
  exact result.trans (by simp [outerBudget]; omega)

theorem flatPackedCenterCandidateInside
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCandidateInsideCode tromino symmetry)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat]
      (flatPackedCenterCandidateInsideCost tromino symmetry
        periodicStrip packed base) := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  let selectedCost := flatPackedCenterAssignmentIsCost symmetry
    periodicStrip packed base
  let absentCost := isZeroCost values selected.toNat selectedCost
  have selectedFit : EvaluatorCodeFits
      (Code.flatPackedCenterAssignmentIsCode symmetry)
      values [selected.toNat] selectedCost := by
    simpa [values, selected, selectedCost] using
      flatPackedCenterAssignmentIs symmetry periodicStrip packed base
  have absentRaw := isZero selectedFit
  have absentFit : EvaluatorCodeFits
      (Code.isZero (Code.flatPackedCenterAssignmentIsCode symmetry))
      values [(!selected).toNat] absentCost := by
    cases selectedEq : selected <;>
      simpa [absentCost, selectedEq] using absentRaw
  have insideFit : EvaluatorCodeFits
      (Code.flatPackedCenterAllSourcesInsideCode tromino symmetry)
      values [inside.toNat]
      (flatPackedCenterAllSourcesInsideCost tromino symmetry
        periodicStrip packed base) := by
    simpa [values, inside] using
      flatPackedCenterAllSourcesInside tromino symmetry
        periodicStrip wellFormed packed base
  have resultRaw := boolOr absentFit insideFit
  have resultFit : EvaluatorCodeFits
      (Code.boolOr
        (Code.isZero (Code.flatPackedCenterAssignmentIsCode symmetry))
        (Code.flatPackedCenterAllSourcesInsideCode tromino symmetry))
      values [((!selected) || inside).toNat]
      (boolOrCost values (!selected).toNat inside.toNat absentCost
        (flatPackedCenterAllSourcesInsideCost tromino symmetry
          periodicStrip packed base)) := by
    cases selectedEq : selected <;> cases insideEq : inside <;>
      simpa [selectedEq, insideEq] using resultRaw
  have semanticEq :
      packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry = ((!selected) || inside) := by
    unfold PackedWindowState.centerSymmetryInsideBool
    change
      (decide
          (packed.assignmentAtCell periodicStrip
            WindowState.center base ≠ some symmetry) || inside) =
        ((!selected) || inside)
    simp [selected]
  simpa [Code.flatPackedCenterCandidateInsideCode,
    flatPackedCenterCandidateInsideCost, values, selected,
    inside, selectedCost, absentCost, semanticEq] using resultFit

theorem flatPackedCenterCandidateInsideBounded
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCandidateInsideCode tromino symmetry)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat]
      (flatPackedCenterCandidateInsideSpaceBound tromino symmetry
        periodicStrip packed base) :=
  (flatPackedCenterCandidateInside tromino symmetry periodicStrip wellFormed
    packed base).mono
      (flatPackedCenterCandidateInsideCost_le_bound tromino symmetry
        periodicStrip packed base)

/-! ## Native quadratic bounds -/

set_option maxRecDepth 1000000

def flatPackedCenterAssignmentIsQuadraticCoefficient : Nat := 10 ^ 200

theorem flatPackedCenterAssignmentIsCost_le_quadratic
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterAssignmentIsCost symmetry periodicStrip packed base ≤
      flatPackedCenterAssignmentIsQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let unit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  let native := flatPackedAssignmentLookupNativeInputSpace
    periodicStrip.motif WindowState.center.val base packed.assignmentWord
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit]
  have nativeBound := flatPackedCenterAssignmentNativeInput_le_candidate
    periodicStrip packed base
  have predicate := flatPackedAssignmentPredicateSpaceBound_le_native_quadratic
    periodicStrip.motif WindowState.center.val base packed.assignmentWord
  have predicateGlobal :
      flatPackedAssignmentPredicateSpaceBound periodicStrip.motif
          WindowState.center.val base packed.assignmentWord ≤
        (4 *
          10000000000000000000000000000000000000000000000000000000000) *
          unit ^ 2 := by
    calc
      _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
          native ^ 2 := predicate
      _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
          (2 * unit) ^ 2 := by
        gcongr
      _ = _ := by ring
  have adapter := flatPackedCenterAssignmentArgumentsCost_le_linear
    periodicStrip packed base
  have adapterGlobal :
      flatPackedCenterAssignmentArgumentsCost periodicStrip packed base ≤
        1000000000 * unit ^ 2 :=
    adapter.trans (Nat.mul_le_mul_left _ (by nlinarith))
  have coefficientBound :
      4 *
          10000000000000000000000000000000000000000000000000000000000 +
        1000000000 ≤ flatPackedCenterAssignmentIsQuadraticCoefficient := by
    native_decide
  change flatPackedAssignmentPredicateSpaceBound periodicStrip.motif
      WindowState.center.val base packed.assignmentWord +
      flatPackedCenterAssignmentArgumentsCost periodicStrip packed base ≤
    flatPackedCenterAssignmentIsQuadraticCoefficient * unit ^ 2
  simp only [unit] at predicateGlobal adapterGlobal
  calc
    _ ≤ (4 *
          10000000000000000000000000000000000000000000000000000000000 +
        1000000000) * unit ^ 2 := by nlinarith
    _ ≤ flatPackedCenterAssignmentIsQuadraticCoefficient * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficientBound

def flatPackedCenterSourceInsideQuadraticCoefficient : Nat := 10 ^ 300

theorem flatPackedCenterSourceInsideCost_le_quadratic
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall : intOffsetAmount (symmetry.act source).2 ≤ 4) :
    flatPackedCenterSourceInsideCost symmetry source
        periodicStrip packed base ≤
      flatPackedCenterSourceInsideQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let unit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  let amount := intOffsetAmount (symmetry.act source).2 + 1
  let native := flatPackedTargetMembershipNativeInputSpace
    (Code.packedSourceColumn symmetry source) (symmetry.act source).2
    periodicStrip.period packed.phase periodicStrip.motif base.2
    packed.assignmentWord
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit]
  have amountBound : amount ≤ 5 := by simp [amount]; omega
  have nativeBound := flatPackedCenterTargetNativeInput_le_candidate
    (Code.packedSourceColumn symmetry source) (symmetry.act source).2
    periodicStrip packed base offsetSmall
  have membership :=
    flatPackedTargetMembershipSpaceBound_le_native_quadratic
      (Code.packedSourceColumn symmetry source) (symmetry.act source).2
      periodicStrip.period packed.phase periodicStrip.motif base.2
      packed.assignmentWord
  have membershipGlobal :
      flatPackedTargetMembershipSpaceBound
          (Code.packedSourceColumn symmetry source) (symmetry.act source).2
          periodicStrip.period packed.phase periodicStrip.motif base.2
          packed.assignmentWord ≤
        (100 * flatPackedTargetMembershipPolynomialCoefficient) *
          unit ^ 2 := by
    calc
      _ ≤ flatPackedTargetMembershipPolynomialCoefficient * amount ^ 2 *
          native ^ 2 := membership
      _ ≤ flatPackedTargetMembershipPolynomialCoefficient * 5 ^ 2 *
          (2 * unit) ^ 2 := by
        gcongr
      _ = _ := by ring
  have adapter := flatPackedCenterSourceInputCost_le_linear
    periodicStrip packed base
  have adapterGlobal :
      flatPackedCenterSourceInputCost periodicStrip packed base ≤
        1000000000 * unit ^ 2 :=
    adapter.trans (Nat.mul_le_mul_left _ (by nlinarith))
  have coefficientBound :
      100 * flatPackedTargetMembershipPolynomialCoefficient + 1000000000 ≤
        flatPackedCenterSourceInsideQuadraticCoefficient := by
    native_decide
  change flatPackedTargetMembershipSpaceBound
      (Code.packedSourceColumn symmetry source) (symmetry.act source).2
      periodicStrip.period packed.phase periodicStrip.motif base.2
      packed.assignmentWord +
      flatPackedCenterSourceInputCost periodicStrip packed base ≤
    flatPackedCenterSourceInsideQuadraticCoefficient * unit ^ 2
  simp only [unit] at membershipGlobal adapterGlobal
  calc
    _ ≤ (100 * flatPackedTargetMembershipPolynomialCoefficient +
        1000000000) * unit ^ 2 := by nlinarith
    _ ≤ flatPackedCenterSourceInsideQuadraticCoefficient * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficientBound

def flatPackedCenterAllSourcesInsideQuadraticCoefficient : Nat := 10 ^ 400

theorem flatPackedCenterAllSourcesInsideSpaceBound_le_quadratic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterAllSourcesInsideSpaceBound tromino symmetry
        periodicStrip packed base ≤
      flatPackedCenterAllSourcesInsideQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let unit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have constantQuadratic : 101 ≤ 101 * unit ^ 2 := by nlinarith
  have coefficientBound :
      2000000 *
          (3 * flatPackedCenterSourceInsideQuadraticCoefficient + 102) ≤
        flatPackedCenterAllSourcesInsideQuadraticCoefficient := by
    native_decide
  have first := flatPackedCenterSourceInsideCost_le_quadratic symmetry (0, 0)
    periodicStrip packed base (by cases symmetry <;> native_decide)
  have second := flatPackedCenterSourceInsideCost_le_quadratic symmetry (1, 0)
    periodicStrip packed base (by cases symmetry <;> native_decide)
  cases tromino with
  | I =>
      have third := flatPackedCenterSourceInsideCost_le_quadratic symmetry
        (2, 0) periodicStrip packed base
        (by cases symmetry <;> native_decide)
      simp only [flatPackedCenterAllSourcesInsideSpaceBound,
        flatPackedCenterAllSourcesInsideSpaceUnit]
      simp only [unit] at first second third unitQuadratic
      calc
        _ ≤ 2000000 *
            ((3 * flatPackedCenterSourceInsideQuadraticCoefficient + 102) *
              unit ^ 2) := by
          gcongr
          nlinarith
        _ = (2000000 *
            (3 * flatPackedCenterSourceInsideQuadraticCoefficient + 102)) *
              unit ^ 2 := by ring
        _ ≤ flatPackedCenterAllSourcesInsideQuadraticCoefficient *
              unit ^ 2 := Nat.mul_le_mul_right (unit ^ 2) coefficientBound
  | L =>
      have third := flatPackedCenterSourceInsideCost_le_quadratic symmetry
        (0, 1) periodicStrip packed base
        (by cases symmetry <;> native_decide)
      simp only [flatPackedCenterAllSourcesInsideSpaceBound,
        flatPackedCenterAllSourcesInsideSpaceUnit]
      simp only [unit] at first second third unitQuadratic
      calc
        _ ≤ 2000000 *
            ((3 * flatPackedCenterSourceInsideQuadraticCoefficient + 102) *
              unit ^ 2) := by
          gcongr
          nlinarith
        _ = (2000000 *
            (3 * flatPackedCenterSourceInsideQuadraticCoefficient + 102)) *
              unit ^ 2 := by ring
        _ ≤ flatPackedCenterAllSourcesInsideQuadraticCoefficient *
              unit ^ 2 := Nat.mul_le_mul_right (unit ^ 2) coefficientBound

def flatPackedCenterCandidateInsideQuadraticCoefficient : Nat := 10 ^ 500

theorem flatPackedCenterCandidateInsideSpaceBound_le_quadratic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCandidateInsideSpaceBound tromino symmetry
        periodicStrip packed base ≤
      flatPackedCenterCandidateInsideQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let unit := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterCandidateInputUnit]
  have assignment := flatPackedCenterAssignmentIsCost_le_quadratic symmetry
    periodicStrip packed base
  have sources := flatPackedCenterAllSourcesInsideSpaceBound_le_quadratic
    tromino symmetry periodicStrip packed base
  have coefficientBound :
      2000000 *
          (flatPackedCenterAssignmentIsQuadraticCoefficient +
            flatPackedCenterAllSourcesInsideQuadraticCoefficient + 102) ≤
        flatPackedCenterCandidateInsideQuadraticCoefficient := by
    native_decide
  simp only [flatPackedCenterCandidateInsideSpaceBound,
    flatPackedCenterCandidateInsideSpaceUnit]
  calc
    _ ≤ 2000000 *
        ((flatPackedCenterAssignmentIsQuadraticCoefficient +
          flatPackedCenterAllSourcesInsideQuadraticCoefficient + 102) *
          unit ^ 2) := by
      gcongr
      nlinarith
    _ = (2000000 *
        (flatPackedCenterAssignmentIsQuadraticCoefficient +
          flatPackedCenterAllSourcesInsideQuadraticCoefficient + 102)) *
          unit ^ 2 := by ring
    _ ≤ flatPackedCenterCandidateInsideQuadraticCoefficient * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficientBound

theorem flatPackedCenterCandidateInsidePolynomialBounded
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCandidateInsideCode tromino symmetry)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat]
      (flatPackedCenterCandidateInsideQuadraticCoefficient *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2) :=
  (flatPackedCenterCandidateInsideBounded tromino symmetry periodicStrip
    wellFormed packed base).mono
      (flatPackedCenterCandidateInsideSpaceBound_le_quadratic tromino symmetry
        periodicStrip packed base)

end EvaluatorCodeFits
end PartrecToTM2
end Turing

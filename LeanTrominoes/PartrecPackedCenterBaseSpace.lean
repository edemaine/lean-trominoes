import LeanTrominoes.PartrecPackedCenterBase
import LeanTrominoes.PartrecPackedCenterCoverageSpace
import LeanTrominoes.PartrecPackedCenterSymmetriesSpace
import LeanTrominoes.PartrecPackedNormalizedAtSpace

/-!
# Evaluator-space certificate for packed center validity at one base

This file fits the direct phase comparison, the guarded containment and
coverage disjunctions, and their final conjunction at one motif occurrence.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

private theorem boolOr_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolOr leftCode rightCode) values
      [(left || right).toNat]
      (boolOrCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolOr leftFit rightFit
  cases left <;> cases right <;> simpa using combined

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

private theorem packedCenterBoolAndCost_le_budget
    (values : List Nat) (left right : Bool)
    (leftCost rightCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget) :
    boolAndCost values left.toNat right.toNat leftCost rightCost ≤
      1000 * (budget + 1) := by
  have headSpace :=
    listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  apply boolAndCost_le_budget values left.toNat right.toNat
    leftCost rightCost budget
  · cases left <;> simp
  · cases right <;> simp
  · omega
  · omega
  · rw [← Nat.succ_eq_add_one]
    omega
  · exact leftCostBound
  · exact rightCostBound
  · omega

private theorem packedCenterBoolOrCost_le_budget
    (values : List Nat) (left right : Bool)
    (leftCost rightCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget) :
    boolOrCost values left.toNat right.toNat leftCost rightCost ≤
      1000 * (budget + 1) := by
  have headSpace :=
    listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  apply boolOrCost_le_budget values left.toNat right.toNat
    leftCost rightCost budget
  · cases left <;> simp
  · cases right <;> simp
  · omega
  · omega
  · rw [← Nat.succ_eq_add_one]
    omega
  · exact leftCostBound
  · exact rightCostBound
  · omega

private theorem packedCenterIsZeroBoolCost_le_budget
    (values : List Nat) (value : Bool)
    (valueCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (valueCostBound : valueCost ≤ budget)
    (budgetLarge : 100 ≤ budget) :
    isZeroCost values value.toNat valueCost ≤
      1000 * (budget + 1) := by
  have headSpace :=
    listCodeEncodedListSpace_singleton_headI_le values
  have headBitsInput :
      (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
    simpa [encodedListSpace_cons] using headSpace
  have successorBits := listCodeEncodeNat_succ_length_le values.headI
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  apply isZeroCost_le_budget values value.toNat valueCost budget
  · omega
  · cases value <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  · cases value <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits] <;> omega
  · omega
  · rw [← Nat.succ_eq_add_one]
    omega
  · exact valueCostBound
  · omega

def packedCenterBaseCoordinateArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let restWord := prependCost values [Encodable.encode base]
    [packed.assignmentWord] (getCost 3 values) (getCost 5 values)
  let restColumn := prependCost values [WindowState.center.val]
    [Encodable.encode base, packed.assignmentWord]
    (numeralCost WindowState.center.val values) restWord
  let restMotif := prependCost values
    [Encodable.encode periodicStrip.motif]
    [WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    (getCost 2 values) restColumn
  let restPhase := prependCost values [packed.phase]
    [Encodable.encode periodicStrip.motif,
      WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    (getCost 1 values) restMotif
  let syntheticPeriodCost := succCost [packed.phase] + getCost 1 values
  prependCost values [packed.phase + 1]
    [packed.phase, Encodable.encode periodicStrip.motif,
      WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    syntheticPeriodCost restPhase

theorem packedCenterBaseCoordinateArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.packedCenterBaseCoordinateArgumentsCode
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [packed.phase + 1, packed.phase,
        Encodable.encode periodicStrip.motif,
        WindowState.center.val, Encodable.encode base,
        packed.assignmentWord]
      (packedCenterBaseCoordinateArgumentsCost
        periodicStrip packed base) := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  have restWord := prepend (get 3 values) (get 5 values)
  have restColumn := prepend
    (numeral WindowState.center.val values) restWord
  have restMotif := prepend (get 2 values) restColumn
  have restPhase := prepend (get 1 values) restMotif
  have syntheticPeriod := comp (succ_named [packed.phase]) (get 1 values)
  simpa [Code.packedCenterBaseCoordinateArgumentsCode,
    packedCenterBaseCoordinateArgumentsCost,
    Code.packedCenterCandidateInput,
    Code.numeral, numeralCost, prependCost, values] using
    prepend syntheticPeriod restPhase

theorem packedCenterBaseCoordinateArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBaseCoordinateArgumentsCost periodicStrip packed base ≤
      10000000000 *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let unit := encodedListSpace values + 1
  have get1 := listCodeGetCost_le_linear 1 values
  have get2 := listCodeGetCost_le_linear 2 values
  have get3 := listCodeGetCost_le_linear 3 values
  have get5 := listCodeGetCost_le_linear 5 values
  have zeroBound := listCodeZeroCost_le_linear values
  have addSmall :
      addConstCost WindowState.center.val [0] ≤ 100000 := by
    native_decide
  have centerBits :
      (Computability.encodeNat WindowState.center.val).length ≤ 100 := by
    native_decide
  have numeralBound :
      numeralCost WindowState.center.val values ≤
        1000000 * unit := by
    simp only [numeralCost]
    omega
  have phaseSuccessorBits :=
    listCodeEncodeNat_succ_length_le packed.phase
  change packedCenterBaseCoordinateArgumentsCost
      periodicStrip packed base ≤ 10000000000 * unit
  dsimp only [unit] at *
  simp [packedCenterBaseCoordinateArgumentsCost,
    prependCost, succCost, values,
    Code.packedCenterCandidateInput,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

def packedCenterBasePhaseEqualCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedNormalizedAtCoordinateCost
      (packed.phase + 1) packed.phase periodicStrip.motif
      WindowState.center.val base packed.assignmentWord +
    packedCenterBaseCoordinateArgumentsCost
      periodicStrip packed base

theorem packedCenterBasePhaseEqual
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    let equal := decide (base.1 = (packed.phase : Int))
    EvaluatorCodeFits Code.packedCenterBasePhaseEqualCode
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [equal.toNat]
      (packedCenterBasePhaseEqualCost periodicStrip packed base) := by
  simp only
  let nonnegative :=
    if IntEncoding.sign base.1 = 0 then 1 else 0
  let magnitudeEqual :=
    if IntEncoding.magnitude base.1 = packed.phase then 1 else 0
  have coordinate := packedNormalizedAtCoordinate
    (packed.phase + 1) packed.phase periodicStrip.motif
    WindowState.center.val base packed.assignmentWord
  simp only [Code.packedCenterSyntheticPhase_eq] at coordinate
  change EvaluatorCodeFits Code.packedNormalizedAtCoordinateCode _
    [if nonnegative = 0 ∨ magnitudeEqual = 0 then 0 else 1] _
    at coordinate
  have rawTagEq :
      (if nonnegative = 0 ∨ magnitudeEqual = 0 then 0 else 1) =
        (decide (base.1 = (packed.phase : Int))).toNat := by
    have tag := Code.packedNormalizedAtCoordinateTag_eq
      (packed.phase + 1) packed.phase WindowState.center.val base
    rw [Code.packedCenterSyntheticPhase_eq] at tag
    simpa [nonnegative, magnitudeEqual] using tag
  rw [rawTagEq] at coordinate
  simpa [Code.packedCenterBasePhaseEqualCode,
    packedCenterBasePhaseEqualCost] using
    comp coordinate
      (packedCenterBaseCoordinateArguments periodicStrip packed base)

def packedCenterBasePhaseEqualSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedNormalizedAtSpaceBound (packed.phase + 1) packed.phase
      (Encodable.encode periodicStrip.motif) WindowState.center.val
      (Encodable.encode base) packed.assignmentWord +
    10000000000 *
      packedCenterCandidateInputUnit periodicStrip packed base

theorem packedCenterBasePhaseEqualCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBasePhaseEqualCost periodicStrip packed base ≤
      packedCenterBasePhaseEqualSpaceBound periodicStrip packed base := by
  exact Nat.add_le_add
    (packedNormalizedAtCoordinateCost_le_linear
      (packed.phase + 1) packed.phase periodicStrip.motif
      WindowState.center.val base packed.assignmentWord)
    (packedCenterBaseCoordinateArgumentsCost_le_linear
      periodicStrip packed base)

def packedCenterBasePhaseDifferentCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let equal := decide (base.1 = (packed.phase : Int))
  isZeroCost values equal.toNat
    (packedCenterBasePhaseEqualCost periodicStrip packed base)

theorem packedCenterBasePhaseDifferent
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.packedCenterBasePhaseDifferentCode
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(decide (base.1 ≠ (packed.phase : Int))).toNat]
      (packedCenterBasePhaseDifferentCost
        periodicStrip packed base) := by
  let equal := decide (base.1 = (packed.phase : Int))
  have equalFit :
      EvaluatorCodeFits Code.packedCenterBasePhaseEqualCode
        (Code.packedCenterCandidateInput periodicStrip packed base)
        [equal.toNat]
        (packedCenterBasePhaseEqualCost periodicStrip packed base) := by
    simpa [equal] using packedCenterBasePhaseEqual
      periodicStrip packed base
  have result := isZero equalFit
  by_cases equality : base.1 = (packed.phase : Int)
  · simpa [Code.packedCenterBasePhaseDifferentCode,
      packedCenterBasePhaseDifferentCost, equal, equality] using result
  · simpa [Code.packedCenterBasePhaseDifferentCode,
      packedCenterBasePhaseDifferentCost, equal, equality] using result

def packedCenterBasePhaseDifferentSpaceUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterBasePhaseEqualSpaceBound periodicStrip packed base +
    packedCenterCandidateInputUnit periodicStrip packed base + 100

def packedCenterBasePhaseDifferentSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (packedCenterBasePhaseDifferentSpaceUnit
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem packedCenterBasePhaseDifferentCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBasePhaseDifferentCost periodicStrip packed base ≤
      packedCenterBasePhaseDifferentSpaceBound
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let equal := decide (base.1 = (packed.phase : Int))
  let equalCost := packedCenterBasePhaseEqualCost
    periodicStrip packed base
  let budget := packedCenterBasePhaseDifferentSpaceUnit
    periodicStrip packed base
  apply packedCenterIsZeroBoolCost_le_budget
  · simp only [budget, packedCenterBasePhaseDifferentSpaceUnit,
      packedCenterCandidateInputUnit, values]
    omega
  · have bound := packedCenterBasePhaseEqualCost_le_linear
      periodicStrip packed base
    simp only [equalCost, budget,
      packedCenterBasePhaseDifferentSpaceUnit]
    omega
  · simp only [budget, packedCenterBasePhaseDifferentSpaceUnit]
    omega

def packedCenterBaseInsideCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  boolOrCost values different.toNat inside.toNat
    (packedCenterBasePhaseDifferentCost periodicStrip packed base)
    (packedCenterAllSymmetriesInsideCost tromino
      periodicStrip packed base)

theorem packedCenterBaseInside
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.packedCenterBaseInsideCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(packed.centerBaseInsideBool
        tromino periodicStrip base).toNat]
      (packedCenterBaseInsideCost tromino
        periodicStrip packed base) := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  have result := boolOr_fit_bool different inside
    (by
      simpa [different] using
        (packedCenterBasePhaseDifferent periodicStrip packed base))
    (by
      simpa [inside] using
        (packedCenterAllSymmetriesInside tromino periodicStrip
          wellFormed packed base))
  simpa [Code.packedCenterBaseInsideCode,
    packedCenterBaseInsideCost,
    PackedWindowState.centerBaseInsideBool,
    different, inside] using result

def packedCenterBaseInsideSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterBasePhaseDifferentSpaceBound periodicStrip packed base +
    packedCenterAllSymmetriesInsideSpaceBound tromino
      periodicStrip packed base +
    packedCenterCandidateInputUnit periodicStrip packed base + 100

def packedCenterBaseInsideSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (packedCenterBaseInsideSpaceUnit tromino
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem packedCenterBaseInsideCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBaseInsideCost tromino periodicStrip packed base ≤
      packedCenterBaseInsideSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let inside := TrominoAssignment.squareSymmetryList.all fun symmetry =>
    packed.centerSymmetryInsideBool tromino periodicStrip base symmetry
  let differentCost := packedCenterBasePhaseDifferentCost
    periodicStrip packed base
  let insideCost := packedCenterAllSymmetriesInsideCost tromino
    periodicStrip packed base
  let budget := packedCenterBaseInsideSpaceUnit tromino
    periodicStrip packed base
  apply packedCenterBoolOrCost_le_budget
  · simp only [budget, packedCenterBaseInsideSpaceUnit,
      packedCenterCandidateInputUnit, values]
    omega
  · have bound := packedCenterBasePhaseDifferentCost_le_linear
      periodicStrip packed base
    simp only [differentCost, budget, packedCenterBaseInsideSpaceUnit]
    omega
  · have bound := packedCenterAllSymmetriesInsideCost_le_linear
      tromino periodicStrip packed base
    simp only [insideCost, budget, packedCenterBaseInsideSpaceUnit]
    omega

def packedCenterBaseCoveredCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  boolOrCost values different.toNat covered.toNat
    (packedCenterBasePhaseDifferentCost periodicStrip packed base)
    (packedCenterExactlyOneCoveringCost tromino
      periodicStrip packed base)

theorem packedCenterBaseCovered
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.packedCenterBaseCoveredCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(packed.centerBaseCoveredBool
        tromino periodicStrip base).toNat]
      (packedCenterBaseCoveredCost tromino
        periodicStrip packed base) := by
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  have result := boolOr_fit_bool different covered
    (by
      simpa [different] using
        (packedCenterBasePhaseDifferent periodicStrip packed base))
    (by
      simpa [covered] using
        (packedCenterExactlyOneCovering
          tromino periodicStrip packed base))
  simpa [Code.packedCenterBaseCoveredCode,
    packedCenterBaseCoveredCost,
    PackedWindowState.centerBaseCoveredBool,
    different, covered] using result

def packedCenterBaseCoveredSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterBasePhaseDifferentSpaceBound periodicStrip packed base +
    packedCenterExactlyOneCoveringSpaceBound tromino
      periodicStrip packed base +
    packedCenterCandidateInputUnit periodicStrip packed base + 100

def packedCenterBaseCoveredSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (packedCenterBaseCoveredSpaceUnit tromino
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem packedCenterBaseCoveredCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBaseCoveredCost tromino periodicStrip packed base ≤
      packedCenterBaseCoveredSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let different := decide (base.1 ≠ (packed.phase : Int))
  let covered := decide ((packed.activePlacementList
    tromino periodicStrip base.2).length = 1)
  let differentCost := packedCenterBasePhaseDifferentCost
    periodicStrip packed base
  let coveredCost := packedCenterExactlyOneCoveringCost tromino
    periodicStrip packed base
  let budget := packedCenterBaseCoveredSpaceUnit tromino
    periodicStrip packed base
  apply packedCenterBoolOrCost_le_budget
  · simp only [budget, packedCenterBaseCoveredSpaceUnit,
      packedCenterCandidateInputUnit, values]
    omega
  · have bound := packedCenterBasePhaseDifferentCost_le_linear
      periodicStrip packed base
    simp only [differentCost, budget,
      packedCenterBaseCoveredSpaceUnit]
    omega
  · have bound := packedCenterExactlyOneCoveringCost_le_linear
      tromino periodicStrip packed base
    simp only [coveredCost, budget, packedCenterBaseCoveredSpaceUnit]
    omega

def packedCenterBaseValidCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  boolAndCost values
    (packed.centerBaseInsideBool tromino periodicStrip base).toNat
    (packed.centerBaseCoveredBool tromino periodicStrip base).toNat
    (packedCenterBaseInsideCost tromino periodicStrip packed base)
    (packedCenterBaseCoveredCost tromino periodicStrip packed base)

def packedCenterBaseValidSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterBaseInsideSpaceBound tromino periodicStrip packed base +
    packedCenterBaseCoveredSpaceBound tromino periodicStrip packed base +
    packedCenterCandidateInputUnit periodicStrip packed base + 100

def packedCenterBaseValidSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000 *
    (packedCenterBaseValidSpaceUnit tromino
      periodicStrip packed base + 1)

set_option linter.unusedSimpArgs false in
theorem packedCenterBaseValidCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterBaseValidCost tromino periodicStrip packed base ≤
      packedCenterBaseValidSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let inside := packed.centerBaseInsideBool tromino periodicStrip base
  let covered := packed.centerBaseCoveredBool tromino periodicStrip base
  let insideCost := packedCenterBaseInsideCost tromino
    periodicStrip packed base
  let coveredCost := packedCenterBaseCoveredCost tromino
    periodicStrip packed base
  let budget := packedCenterBaseValidSpaceUnit tromino
    periodicStrip packed base
  apply packedCenterBoolAndCost_le_budget
  · simp only [budget, packedCenterBaseValidSpaceUnit,
      packedCenterCandidateInputUnit, values]
    omega
  · have bound := packedCenterBaseInsideCost_le_linear
      tromino periodicStrip packed base
    simp only [insideCost, budget, packedCenterBaseValidSpaceUnit]
    omega
  · have bound := packedCenterBaseCoveredCost_le_linear
      tromino periodicStrip packed base
    simp only [coveredCost, budget, packedCenterBaseValidSpaceUnit]
    omega

/-- Exact fitted execution of both center conditions at one motif base. -/
theorem packedCenterBaseValid
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits (Code.packedCenterBaseValidCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [((packed.centerBaseInsideBool tromino periodicStrip base) &&
        packed.centerBaseCoveredBool tromino periodicStrip base).toNat]
      (packedCenterBaseValidCost tromino
        periodicStrip packed base) := by
  simpa [Code.packedCenterBaseValidCode,
    packedCenterBaseValidCost] using
    boolAnd_fit_bool
      (packed.centerBaseInsideBool tromino periodicStrip base)
      (packed.centerBaseCoveredBool tromino periodicStrip base)
      (packedCenterBaseInside tromino periodicStrip
        wellFormed packed base)
      (packedCenterBaseCovered tromino periodicStrip packed base)

end EvaluatorCodeFits

end PartrecToTM2
end Turing

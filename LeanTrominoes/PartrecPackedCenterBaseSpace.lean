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

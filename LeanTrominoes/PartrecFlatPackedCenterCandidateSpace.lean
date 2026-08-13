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

end EvaluatorCodeFits
end PartrecToTM2
end Turing

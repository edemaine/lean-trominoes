import LeanTrominoes.PartrecPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecPackedCenterCandidate
import LeanTrominoes.PartrecPackedTargetMembershipSpace

/-!
# Evaluator-space certificate for packed center candidates

This file fits the fixed-width center-candidate program: center assignment
selection, each translated source-cell membership call, the three-source
conjunction, and the final implication.  All Boolean folds have fixed size
because a tromino has exactly three source cells.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def packedCenterAssignmentArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let restBase :=
    prependCost values [Encodable.encode base]
      [packed.assignmentWord]
      (getCost 3 values) (getCost 5 values)
  let restColumn :=
    prependCost values [WindowState.center.val]
      [Encodable.encode base, packed.assignmentWord]
      (numeralCost WindowState.center.val values) restBase
  prependCost values [Encodable.encode periodicStrip.motif]
    [WindowState.center.val, Encodable.encode base,
      packed.assignmentWord]
    (getCost 2 values) restColumn

theorem packedCenterAssignmentArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.packedCenterAssignmentArgumentsCode
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [Encodable.encode periodicStrip.motif,
        WindowState.center.val, Encodable.encode base,
        packed.assignmentWord]
      (packedCenterAssignmentArgumentsCost
        periodicStrip packed base) := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  have restBase := prepend (get 3 values) (get 5 values)
  have restColumn :=
    prepend (numeral WindowState.center.val values) restBase
  have result := prepend (get 2 values) restColumn
  simpa [Code.packedCenterAssignmentArgumentsCode,
    packedCenterAssignmentArgumentsCost,
    Code.packedCenterCandidateInput,
    Code.numeral, numeralCost, prependCost, values] using result

def packedCenterAssignmentIsCost
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedAssignmentIsCost (some symmetry) periodicStrip.motif
      WindowState.center.val base packed.assignmentWord +
    packedCenterAssignmentArgumentsCost periodicStrip packed base

theorem packedCenterAssignmentIs
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    let selected := decide
      (packed.assignmentAtCell periodicStrip
        WindowState.center base = some symmetry)
    EvaluatorCodeFits
      (Code.packedCenterAssignmentIsCode symmetry)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [selected.toNat]
      (packedCenterAssignmentIsCost
        symmetry periodicStrip packed base) := by
  simp only
  simpa [Code.packedCenterAssignmentIsCode,
    packedCenterAssignmentIsCost] using
    comp
      (packedAssignmentIs_semantic (some symmetry)
        periodicStrip packed WindowState.center base)
      (packedCenterAssignmentArguments periodicStrip packed base)

def packedCenterSourceInputCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let restWord :=
    prependCost values [Encodable.encode base.2]
      [packed.assignmentWord]
      (getCost 4 values) (getCost 5 values)
  let restMotif :=
    prependCost values [Encodable.encode periodicStrip.motif]
      [Encodable.encode base.2, packed.assignmentWord]
      (getCost 2 values) restWord
  let restPhase :=
    prependCost values [packed.phase]
      [Encodable.encode periodicStrip.motif,
        Encodable.encode base.2, packed.assignmentWord]
      (getCost 1 values) restMotif
  prependCost values [periodicStrip.period]
    [packed.phase, Encodable.encode periodicStrip.motif,
      Encodable.encode base.2, packed.assignmentWord]
    (getCost 0 values) restPhase

theorem packedCenterSourceInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits Code.packedCenterSourceInputCode
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        Encodable.encode base.2, packed.assignmentWord]
      (packedCenterSourceInputCost periodicStrip packed base) := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  have restWord := prepend (get 4 values) (get 5 values)
  have restMotif := prepend (get 2 values) restWord
  have restPhase := prepend (get 1 values) restMotif
  have result := prepend (get 0 values) restPhase
  simpa [Code.packedCenterSourceInputCode,
    packedCenterSourceInputCost,
    Code.packedCenterCandidateInput,
    prependCost, values] using result

def packedCenterSourceInsideCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedTargetMembershipCost
      (Code.packedSourceColumn symmetry source)
      (symmetry.act source).2
      periodicStrip.period packed.phase periodicStrip.motif
      base.2 packed.assignmentWord +
    packedCenterSourceInputCost periodicStrip packed base

theorem packedCenterSourceInside
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterSourceInsideCode symmetry source)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(packed.centerSourceInsideBool periodicStrip
        base symmetry source).toNat]
      (packedCenterSourceInsideCost symmetry source
        periodicStrip packed base) := by
  have horizontal :
      (symmetry.act source).1 =
        (Code.packedSourceColumn symmetry source).displacement :=
    (Code.packedSourceColumn_displacement
      tromino symmetry source sourceMember).symm
  have membership := packedTargetMembership_contains
    (Code.packedSourceColumn symmetry source)
    (symmetry.act source).2 periodicStrip wellFormed packed base.2
  have membershipSemantic :
      EvaluatorCodeFits
        (Code.packedTargetMembershipCode
          (Code.packedSourceColumn symmetry source)
          (symmetry.act source).2)
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          Encodable.encode base.2, packed.assignmentWord]
        [(packed.centerSourceInsideBool periodicStrip
          base symmetry source).toNat]
        (packedTargetMembershipCost
          (Code.packedSourceColumn symmetry source)
          (symmetry.act source).2 periodicStrip.period packed.phase
          periodicStrip.motif base.2 packed.assignmentWord) := by
    simpa [PackedWindowState.centerSourceInsideBool,
      Cell.add, horizontal] using membership
  simpa [Code.packedCenterSourceInsideCode,
    packedCenterSourceInsideCost] using
    comp membershipSemantic
      (packedCenterSourceInput periodicStrip packed base)

private def boolAndThreeCost
    (values : List Nat)
    (first second third : Bool)
    (firstCost secondCost thirdCost : Nat) : Nat :=
  let tailCost := boolAndCost values
    second.toNat third.toNat secondCost thirdCost
  boolAndCost values first.toNat (second && third).toNat
    firstCost tailCost

private theorem boolAndThree
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
      (boolAndThreeCost values first second third
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
    simpa [boolAndThreeCost] using resultRaw

def packedCenterAllSourcesInsideCost
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  match tromino with
  | .I =>
      boolAndThreeCost values
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (0, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (1, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (2, 0))
        (packedCenterSourceInsideCost symmetry (0, 0)
          periodicStrip packed base)
        (packedCenterSourceInsideCost symmetry (1, 0)
          periodicStrip packed base)
        (packedCenterSourceInsideCost symmetry (2, 0)
          periodicStrip packed base)
  | .L =>
      boolAndThreeCost values
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (0, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (1, 0))
        (packed.centerSourceInsideBool periodicStrip
          base symmetry (0, 1))
        (packedCenterSourceInsideCost symmetry (0, 0)
          periodicStrip packed base)
        (packedCenterSourceInsideCost symmetry (1, 0)
          periodicStrip packed base)
        (packedCenterSourceInsideCost symmetry (0, 1)
          periodicStrip packed base)

theorem packedCenterAllSourcesInside
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    let inside :=
      (TrominoAssignment.trominoCellList tromino).all fun source =>
        packed.centerSourceInsideBool periodicStrip base symmetry source
    EvaluatorCodeFits
      (Code.packedCenterAllSourcesInsideCode tromino symmetry)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [inside.toNat]
      (packedCenterAllSourcesInsideCost tromino symmetry
        periodicStrip packed base) := by
  simp only
  cases tromino with
  | I =>
      simpa [Code.packedCenterAllSourcesInsideCode,
        packedCenterAllSourcesInsideCost,
        TrominoAssignment.trominoCellList] using
        boolAndThree
          (Code.packedCenterSourceInsideCode symmetry (0, 0))
          (Code.packedCenterSourceInsideCode symmetry (1, 0))
          (Code.packedCenterSourceInsideCode symmetry (2, 0))
          (Code.packedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (2, 0))
          (packedCenterSourceInsideCost symmetry (0, 0)
            periodicStrip packed base)
          (packedCenterSourceInsideCost symmetry (1, 0)
            periodicStrip packed base)
          (packedCenterSourceInsideCost symmetry (2, 0)
            periodicStrip packed base)
          (packedCenterSourceInside .I symmetry (0, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInside .I symmetry (1, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInside .I symmetry (2, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
  | L =>
      simpa [Code.packedCenterAllSourcesInsideCode,
        packedCenterAllSourcesInsideCost,
        TrominoAssignment.trominoCellList] using
        boolAndThree
          (Code.packedCenterSourceInsideCode symmetry (0, 0))
          (Code.packedCenterSourceInsideCode symmetry (1, 0))
          (Code.packedCenterSourceInsideCode symmetry (0, 1))
          (Code.packedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 1))
          (packedCenterSourceInsideCost symmetry (0, 0)
            periodicStrip packed base)
          (packedCenterSourceInsideCost symmetry (1, 0)
            periodicStrip packed base)
          (packedCenterSourceInsideCost symmetry (0, 1)
            periodicStrip packed base)
          (packedCenterSourceInside .L symmetry (0, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInside .L symmetry (1, 0)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInside .L symmetry (0, 1)
            (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)

def packedCenterCandidateInsideCost
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  let selectedCost :=
    packedCenterAssignmentIsCost symmetry periodicStrip packed base
  let absentCost :=
    isZeroCost values selected.toNat selectedCost
  boolOrCost values (!selected).toNat inside.toNat absentCost
    (packedCenterAllSourcesInsideCost tromino symmetry
      periodicStrip packed base)

/-- Exact fitted execution of one center-containment implication. -/
theorem packedCenterCandidateInside
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterCandidateInsideCode tromino symmetry)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat]
      (packedCenterCandidateInsideCost tromino symmetry
        periodicStrip packed base) := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  let selectedCost :=
    packedCenterAssignmentIsCost symmetry periodicStrip packed base
  let absentCost := isZeroCost values selected.toNat selectedCost
  have selectedFit :
      EvaluatorCodeFits
        (Code.packedCenterAssignmentIsCode symmetry)
        values [selected.toNat] selectedCost := by
    simpa [values, selected, selectedCost] using
      packedCenterAssignmentIs symmetry periodicStrip packed base
  have absentRaw := isZero selectedFit
  have absentFit :
      EvaluatorCodeFits
        (Code.isZero (Code.packedCenterAssignmentIsCode symmetry))
        values [(!selected).toNat] absentCost := by
    cases selectedEq : selected <;>
      simpa [absentCost, selectedEq] using absentRaw
  have insideFit :
      EvaluatorCodeFits
        (Code.packedCenterAllSourcesInsideCode tromino symmetry)
        values [inside.toNat]
        (packedCenterAllSourcesInsideCost tromino symmetry
          periodicStrip packed base) := by
    simpa [values, inside] using
      packedCenterAllSourcesInside tromino symmetry
        periodicStrip wellFormed packed base
  have resultRaw := boolOr absentFit insideFit
  have resultFit :
      EvaluatorCodeFits
        (Code.boolOr
          (Code.isZero (Code.packedCenterAssignmentIsCode symmetry))
          (Code.packedCenterAllSourcesInsideCode tromino symmetry))
        values [((!selected) || inside).toNat]
        (boolOrCost values (!selected).toNat inside.toNat absentCost
          (packedCenterAllSourcesInsideCost tromino symmetry
            periodicStrip packed base)) := by
    cases selectedEq : selected <;> cases insideEq : inside <;>
      simpa [selectedEq, insideEq] using resultRaw
  have semanticEq :
      packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry =
        ((!selected) || inside) := by
    unfold PackedWindowState.centerSymmetryInsideBool
    change
      (decide
          (packed.assignmentAtCell periodicStrip
            WindowState.center base ≠ some symmetry) || inside) =
        ((!selected) || inside)
    simp [selected]
  simpa [Code.packedCenterCandidateInsideCode,
    packedCenterCandidateInsideCost, values, selected,
    inside, selectedCost, absentCost, semanticEq] using resultFit

end EvaluatorCodeFits

end PartrecToTM2
end Turing

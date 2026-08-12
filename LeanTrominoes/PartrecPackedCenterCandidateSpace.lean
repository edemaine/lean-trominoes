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

/-- Native input footprint shared by the fixed-width center-candidate
adapters and Boolean combinators. -/
def packedCenterCandidateInputUnit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  encodedListSpace
      (Code.packedCenterCandidateInput periodicStrip packed base) + 1

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

theorem packedCenterAssignmentArgumentsCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterAssignmentArgumentsCost periodicStrip packed base ≤
      1000000000 *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let unit := encodedListSpace values + 1
  have unitPositive : 1 ≤ unit := by simp [unit]
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
  change packedCenterAssignmentArgumentsCost
      periodicStrip packed base ≤ 1000000000 * unit
  dsimp only [unit] at *
  simp [packedCenterAssignmentArgumentsCost, prependCost,
    values, Code.packedCenterCandidateInput,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

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

/-- Workspace envelope for selecting the center assignment. -/
def packedCenterAssignmentIsSpaceBound
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedAssignmentIsSpaceBound
      (Encodable.encode periodicStrip.motif) WindowState.center.val
      (Encodable.encode base) packed.assignmentWord +
    1000000000 *
      packedCenterCandidateInputUnit periodicStrip packed base

theorem packedCenterAssignmentIsCost_le_linear
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterAssignmentIsCost symmetry periodicStrip packed base ≤
      packedCenterAssignmentIsSpaceBound
        periodicStrip packed base := by
  exact Nat.add_le_add
    (packedAssignmentIsCost_le_linear
      (some symmetry) periodicStrip.motif WindowState.center.val
      base packed.assignmentWord)
    (packedCenterAssignmentArgumentsCost_le_linear
      periodicStrip packed base)

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

theorem packedCenterSourceInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterSourceInputCost periodicStrip packed base ≤
      1000000000 *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let unit := encodedListSpace values + 1
  have get0 := listCodeGetCost_le_linear 0 values
  have get1 := listCodeGetCost_le_linear 1 values
  have get2 := listCodeGetCost_le_linear 2 values
  have get4 := listCodeGetCost_le_linear 4 values
  have get5 := listCodeGetCost_le_linear 5 values
  change packedCenterSourceInputCost periodicStrip packed base ≤
    1000000000 * unit
  dsimp only [unit] at *
  simp [packedCenterSourceInputCost, prependCost,
    values, Code.packedCenterCandidateInput,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

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

/-- Workspace envelope for testing one translated source cell. -/
def packedCenterSourceInsideSpaceBound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000000000000000000000000000000000000000000000000000000 *
      (intOffsetAmount (symmetry.act source).2 + 1) *
      packedTargetMembershipUnit
        (Code.packedSourceColumn symmetry source)
        (symmetry.act source).2 periodicStrip.period packed.phase
        periodicStrip.motif base.2 packed.assignmentWord +
    1000000000 *
      packedCenterCandidateInputUnit periodicStrip packed base

theorem packedCenterSourceInsideCost_le_linear
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterSourceInsideCost symmetry source
        periodicStrip packed base ≤
      packedCenterSourceInsideSpaceBound symmetry source
        periodicStrip packed base := by
  exact Nat.add_le_add
    (packedTargetMembershipCost_le_linear
      (Code.packedSourceColumn symmetry source)
      (symmetry.act source).2 periodicStrip.period packed.phase
      periodicStrip.motif base.2 packed.assignmentWord)
    (packedCenterSourceInputCost_le_linear
      periodicStrip packed base)

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

private theorem boolAndThreeCost_le_budget
    (values : List Nat)
    (first second third : Bool)
    (firstCost secondCost thirdCost budget : Nat)
    (valuesBound : encodedListSpace values + 1 ≤ budget)
    (firstCostBound : firstCost ≤ budget)
    (secondCostBound : secondCost ≤ budget)
    (thirdCostBound : thirdCost ≤ budget) :
    boolAndThreeCost values first second third
        firstCost secondCost thirdCost ≤
      2000000 * (budget + 1) := by
  have budgetPositive : 1 ≤ budget := by omega
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
  have firstSmall : first.toNat ≤ 1 := by cases first <;> simp
  have secondSmall : second.toNat ≤ 1 := by cases second <;> simp
  have thirdSmall : third.toNat ≤ 1 := by cases third <;> simp
  have tail := boolAndCost_le_budget values
    second.toNat third.toNat secondCost thirdCost budget
    secondSmall thirdSmall (by omega) headBits headSuccessorBits
    secondCostBound thirdCostBound budgetPositive
  let outerBudget := 1000 * (budget + 1)
  have outerPositive : 1 ≤ outerBudget := by
    simp only [outerBudget]
    omega
  have inputOuter : encodedListSpace values ≤ outerBudget := by
    simp only [outerBudget]
    omega
  have headOuter :
      (Computability.encodeNat values.headI).length ≤
        outerBudget := headBits.trans (by
          simp only [outerBudget]
          omega)
  have headSuccessorOuter :
      (Computability.encodeNat (values.headI + 1)).length ≤
        outerBudget := headSuccessorBits.trans (by
          simp only [outerBudget]
          omega)
  have firstOuter : firstCost ≤ outerBudget :=
    firstCostBound.trans (by
      simp only [outerBudget]
      omega)
  have tailOuter :
      boolAndCost values second.toNat third.toNat
          secondCost thirdCost ≤ outerBudget := by
    simpa [outerBudget] using tail
  have outer := boolAndCost_le_budget values
    first.toNat (second && third).toNat firstCost
    (boolAndCost values second.toNat third.toNat
      secondCost thirdCost) outerBudget firstSmall
    (by cases second <;> cases third <;> simp)
    inputOuter headOuter headSuccessorOuter firstOuter tailOuter
    outerPositive
  simp only [boolAndThreeCost]
  exact outer.trans (by
    simp only [outerBudget]
    omega)

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

/-- Sum of the three translated membership envelopes and the shared native
input footprint. -/
def packedCenterAllSourcesInsideSpaceUnit
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let inputUnit :=
    packedCenterCandidateInputUnit periodicStrip packed base
  match tromino with
  | .I =>
      packedCenterSourceInsideSpaceBound symmetry (0, 0)
          periodicStrip packed base +
        packedCenterSourceInsideSpaceBound symmetry (1, 0)
          periodicStrip packed base +
        packedCenterSourceInsideSpaceBound symmetry (2, 0)
          periodicStrip packed base + inputUnit + 100
  | .L =>
      packedCenterSourceInsideSpaceBound symmetry (0, 0)
          periodicStrip packed base +
        packedCenterSourceInsideSpaceBound symmetry (1, 0)
          periodicStrip packed base +
        packedCenterSourceInsideSpaceBound symmetry (0, 1)
          periodicStrip packed base + inputUnit + 100

def packedCenterAllSourcesInsideSpaceBound
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  2000000 *
    (packedCenterAllSourcesInsideSpaceUnit tromino symmetry
      periodicStrip packed base + 1)

theorem packedCenterAllSourcesInsideCost_le_linear
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterAllSourcesInsideCost tromino symmetry
        periodicStrip packed base ≤
      packedCenterAllSourcesInsideSpaceBound tromino symmetry
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  cases tromino with
  | I =>
      apply boolAndThreeCost_le_budget
      · simp only [packedCenterAllSourcesInsideSpaceUnit,
          packedCenterCandidateInputUnit]
        omega
      · have bound := packedCenterSourceInsideCost_le_linear
          symmetry (0, 0) periodicStrip packed base
        simp only [packedCenterAllSourcesInsideSpaceUnit]
        omega
      · have bound := packedCenterSourceInsideCost_le_linear
          symmetry (1, 0) periodicStrip packed base
        simp only [packedCenterAllSourcesInsideSpaceUnit]
        omega
      · have bound := packedCenterSourceInsideCost_le_linear
          symmetry (2, 0) periodicStrip packed base
        simp only [packedCenterAllSourcesInsideSpaceUnit]
        omega
  | L =>
      apply boolAndThreeCost_le_budget
      · simp only [packedCenterAllSourcesInsideSpaceUnit,
          packedCenterCandidateInputUnit]
        omega
      · have bound := packedCenterSourceInsideCost_le_linear
          symmetry (0, 0) periodicStrip packed base
        simp only [packedCenterAllSourcesInsideSpaceUnit]
        omega
      · have bound := packedCenterSourceInsideCost_le_linear
          symmetry (1, 0) periodicStrip packed base
        simp only [packedCenterAllSourcesInsideSpaceUnit]
        omega
      · have bound := packedCenterSourceInsideCost_le_linear
          symmetry (0, 1) periodicStrip packed base
        simp only [packedCenterAllSourcesInsideSpaceUnit]
        omega

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

/-- One common budget for center assignment selection, three-cell
containment, and the fixed-width Boolean implication. -/
def packedCenterCandidateInsideSpaceUnit
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterAssignmentIsSpaceBound periodicStrip packed base +
    packedCenterAllSourcesInsideSpaceBound tromino symmetry
      periodicStrip packed base +
    packedCenterCandidateInputUnit periodicStrip packed base + 100

def packedCenterCandidateInsideSpaceBound
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  2000000 *
    (packedCenterCandidateInsideSpaceUnit tromino symmetry
      periodicStrip packed base + 1)

set_option maxHeartbeats 800000 in
theorem packedCenterCandidateInsideCost_le_linear
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterCandidateInsideCost tromino symmetry
        periodicStrip packed base ≤
      packedCenterCandidateInsideSpaceBound tromino symmetry
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  let selectedCost :=
    packedCenterAssignmentIsCost symmetry periodicStrip packed base
  let insideCost :=
    packedCenterAllSourcesInsideCost tromino symmetry
      periodicStrip packed base
  let budget := packedCenterCandidateInsideSpaceUnit
    tromino symmetry periodicStrip packed base
  have valuesBound : encodedListSpace values + 1 ≤ budget := by
    simp only [budget, packedCenterCandidateInsideSpaceUnit,
      packedCenterCandidateInputUnit, values]
    omega
  have budgetLarge : 100 ≤ budget := by
    simp only [budget, packedCenterCandidateInsideSpaceUnit]
    omega
  have selectedCostBound : selectedCost ≤ budget := by
    have bound := packedCenterAssignmentIsCost_le_linear
      symmetry periodicStrip packed base
    simp only [selectedCost, budget,
      packedCenterCandidateInsideSpaceUnit]
    omega
  have insideCostBound : insideCost ≤ budget := by
    have bound := packedCenterAllSourcesInsideCost_le_linear
      tromino symmetry periodicStrip packed base
    simp only [insideCost, budget,
      packedCenterCandidateInsideSpaceUnit]
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
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have selectedSpace :
      encodedListSpace [selected.toNat] ≤ budget := by
    cases selected <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  have selectedPredSpace :
      encodedListSpace [selected.toNat.pred] ≤ budget := by
    cases selected <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits] <;> omega
  have absentCostBound := isZeroCost_le_budget values
    selected.toNat selectedCost budget (by omega) selectedSpace
    selectedPredSpace headBits headSuccessorBits selectedCostBound
    (by omega)
  let outerBudget := 1000 * (budget + 1)
  have outerLarge : 1 ≤ outerBudget := by
    simp only [outerBudget]
    omega
  have valuesOuter : encodedListSpace values ≤ outerBudget := by
    simp only [outerBudget]
    omega
  have headOuter :
      (Computability.encodeNat values.headI).length ≤
        outerBudget := headBits.trans (by
          simp only [outerBudget]
          omega)
  have headSuccessorOuter :
      (Computability.encodeNat (values.headI + 1)).length ≤
        outerBudget := headSuccessorBits.trans (by
          simp only [outerBudget]
          omega)
  have absentOuter :
      isZeroCost values selected.toNat selectedCost ≤
        outerBudget := by
    simpa [outerBudget] using absentCostBound
  have insideOuter : insideCost ≤ outerBudget :=
    insideCostBound.trans (by
      simp only [outerBudget]
      omega)
  have result := boolOrCost_le_budget values
    (!selected).toNat inside.toNat
    (isZeroCost values selected.toNat selectedCost) insideCost
    outerBudget
    (by cases selected <;> simp)
    (by cases inside <;> simp)
    valuesOuter headOuter headSuccessorOuter absentOuter insideOuter
    outerLarge
  change boolOrCost values (!selected).toNat inside.toNat
      (isZeroCost values selected.toNat selectedCost) insideCost ≤
    2000000 * (budget + 1)
  exact result.trans (by
    simp only [outerBudget]
    omega)

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

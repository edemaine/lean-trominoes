import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecFlatPackedCenterCoverage
import LeanTrominoes.PartrecFlatPackedCenterCoveringCandidateSpace

/-!
# Evaluator-space certificate for exact-one flat packed center coverage

This file fits the fixed 24-candidate sum and its comparison with one.  The
list recurrence is specialized to a constant-size enumeration in the final
exported theorem.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

/-- Exact evaluator cost of summing a fixed list of active-candidate bits. -/
def flatPackedCenterCoveringCandidateListCountCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List (SquareSymmetry × Cell) -> Nat
  | [] => zeroCost
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
  | candidate :: candidates =>
      let values :=
        Code.flatPackedCenterCandidateInput periodicStrip packed base
      let selected := decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (candidate.1.act candidate.2)) =
          some candidate.1)
      let tailCount := (candidates.filter fun remaining =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (remaining.1.act remaining.2)) =
          some remaining.1).length
      let argumentsCost := prependCost values [selected.toNat]
        [tailCount]
        (flatPackedCenterCoveringCandidateCost
          candidate.1 candidate.2 periodicStrip packed base)
        (flatPackedCenterCoveringCandidateListCountCost
          tromino periodicStrip packed base candidates)
      natAddCost selected.toNat tailCount + argumentsCost

theorem flatPackedCenterCoveringCandidateListCount
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (sourcesValid : ∀ candidate ∈ candidates,
      candidate.2 ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCoveringCandidateListCountCode candidates)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(candidates.filter fun candidate =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (candidate.1.act candidate.2)) =
          some candidate.1).length]
      (flatPackedCenterCoveringCandidateListCountCost tromino
        periodicStrip packed base candidates) := by
  induction candidates with
  | nil =>
      simpa [Code.flatPackedCenterCoveringCandidateListCountCode,
        flatPackedCenterCoveringCandidateListCountCost] using
        zero (Code.flatPackedCenterCandidateInput
          periodicStrip packed base)
  | cons candidate candidates induction =>
      have sourceMember :
          candidate.2 ∈
            TrominoAssignment.trominoCellList tromino :=
        sourcesValid candidate (by simp)
      have tailValid : ∀ remaining ∈ candidates,
          remaining.2 ∈
            TrominoAssignment.trominoCellList tromino := by
        intro remaining remainingMember
        exact sourcesValid remaining (by simp [remainingMember])
      let values :=
        Code.flatPackedCenterCandidateInput periodicStrip packed base
      let selected : Prop :=
        packed.localAssignment periodicStrip
            (Cell.sub (0, base.2)
              (candidate.1.act candidate.2)) =
          some candidate.1
      let selectedBit := decide selected
      let tailCount := (candidates.filter fun remaining =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (remaining.1.act remaining.2)) =
          some remaining.1).length
      let headCost := flatPackedCenterCoveringCandidateCost
        candidate.1 candidate.2 periodicStrip packed base
      let tailCost := flatPackedCenterCoveringCandidateListCountCost
        tromino periodicStrip packed base candidates
      let argumentsCost := prependCost values [selectedBit.toNat]
        [tailCount] headCost tailCost
      have headFit :
          EvaluatorCodeFits
            (Code.flatPackedCenterCoveringCandidateCode
              candidate.1 candidate.2)
            values [selectedBit.toNat] headCost := by
        simpa [values, selected, selectedBit, headCost] using
          flatPackedCenterCoveringCandidate tromino
            candidate.1 candidate.2 sourceMember
            periodicStrip packed base
      have tailFit :
          EvaluatorCodeFits
            (Code.flatPackedCenterCoveringCandidateListCountCode candidates)
            values [tailCount] tailCost := by
        simpa [values, tailCount, tailCost] using induction tailValid
      have argumentsFit :
          EvaluatorCodeFits
            (Code.prepend
              (Code.flatPackedCenterCoveringCandidateCode
                candidate.1 candidate.2)
              (Code.flatPackedCenterCoveringCandidateListCountCode candidates))
            values [selectedBit.toNat, tailCount]
            argumentsCost := by
        simpa [argumentsCost] using prepend headFit tailFit
      have result := comp (natAdd selectedBit.toNat tailCount)
        argumentsFit
      change EvaluatorCodeFits
        (Code.natAddCode.comp
          (Code.prepend
            (Code.flatPackedCenterCoveringCandidateCode
              candidate.1 candidate.2)
            (Code.flatPackedCenterCoveringCandidateListCountCode candidates)))
        values
        [((candidate :: candidates).filter fun remaining =>
          packed.localAssignment periodicStrip
            (Cell.sub (0, base.2)
              (remaining.1.act remaining.2)) =
            some remaining.1).length]
        (natAddCost selectedBit.toNat tailCount + argumentsCost)
      by_cases selectedProof : selected
      · have selectedTrue : selectedBit = true := by
          simp [selectedBit, selectedProof]
        have headTrue :
            decide
              (packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (candidate.1.act candidate.2)) =
                some candidate.1) = true := by
          simpa [selected, selectedBit] using selectedTrue
        have outputEq :
            ((candidate :: candidates).filter fun remaining =>
              packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (remaining.1.act remaining.2)) =
                some remaining.1).length =
              selectedBit.toNat + tailCount := by
          simp only [List.filter_cons, headTrue, ↓reduceIte,
            List.length_cons, tailCount, selectedTrue,
            Bool.toNat_true]
          omega
        rw [outputEq]
        exact result
      · have selectedFalse : selectedBit = false := by
          simp [selectedBit, selectedProof]
        have headFalse :
            decide
              (packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (candidate.1.act candidate.2)) =
                some candidate.1) = false := by
          simpa [selected, selectedBit] using selectedFalse
        have outputEq :
            ((candidate :: candidates).filter fun remaining =>
              packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (remaining.1.act remaining.2)) =
                some remaining.1).length =
              selectedBit.toNat + tailCount := by
          simp only [List.filter_cons, headFalse,
            Bool.false_eq_true, ↓reduceIte, tailCount,
            selectedFalse, Bool.toNat_false, Nat.zero_add]
        rw [outputEq]
        exact result

/-- Recursive workspace envelope for the fixed candidate counter.  The list
length controls the only numeric accumulator exposed by the fold. -/
def flatPackedCenterCoveringCandidateListCountSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List (SquareSymmetry × Cell) → Nat
  | [] =>
      10000 *
        flatPackedCenterCandidateInputUnit periodicStrip packed base
  | candidate :: candidates =>
      let budget :=
        flatPackedCenterCoveringCandidateSpaceBound
            candidate.1 candidate.2 periodicStrip packed base +
          flatPackedCenterCoveringCandidateListCountSpaceBound tromino
            periodicStrip packed base candidates +
          flatPackedCenterCandidateInputUnit periodicStrip packed base +
          (encodedListSpace [1, candidates.length] + 1) +
          (encodedListSpace
            [2 * (candidates.length + 1) + 4] + 1) + 100
      200000000 * (budget + 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem flatPackedCenterCoveringCandidateListCountCost_le_bound
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCoveringCandidateListCountCost tromino
        periodicStrip packed base candidates ≤
      flatPackedCenterCoveringCandidateListCountSpaceBound tromino
        periodicStrip packed base candidates := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  induction candidates with
  | nil =>
      have bound := listCodeZeroCost_le_linear
        (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      change zeroCost
          (Code.flatPackedCenterCandidateInput periodicStrip packed base) ≤
        10000 *
          (encodedListSpace
            (Code.flatPackedCenterCandidateInput periodicStrip packed base) + 10)
      omega
  | cons candidate candidates induction =>
      let selected := decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (candidate.1.act candidate.2)) =
          some candidate.1)
      let tailCount := (candidates.filter fun remaining =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (remaining.1.act remaining.2)) =
          some remaining.1).length
      let headCost := flatPackedCenterCoveringCandidateCost
        candidate.1 candidate.2 periodicStrip packed base
      let tailCost := flatPackedCenterCoveringCandidateListCountCost
        tromino periodicStrip packed base candidates
      let budget :=
        flatPackedCenterCoveringCandidateSpaceBound
            candidate.1 candidate.2 periodicStrip packed base +
          flatPackedCenterCoveringCandidateListCountSpaceBound tromino
            periodicStrip packed base candidates +
          flatPackedCenterCandidateInputUnit periodicStrip packed base +
          (encodedListSpace [1, candidates.length] + 1) +
          (encodedListSpace
            [2 * (candidates.length + 1) + 4] + 1) + 100
      have budgetLarge : 100 ≤ budget := by
        simp only [budget]
        omega
      have valuesBound : encodedListSpace values ≤ budget := by
        simp only [budget, flatPackedCenterCandidateInputUnit, values]
        omega
      have headCostBound : headCost ≤ budget := by
        have bound := flatPackedCenterCoveringCandidateCost_le_bound
          candidate.1 candidate.2 periodicStrip packed base
        simp only [headCost, budget]
        omega
      have tailCostBound : tailCost ≤ budget := by
        simp only [tailCost, budget]
        omega
      have tailCountBound : tailCount ≤ candidates.length := by
        simp only [tailCount]
        exact List.length_filter_le _ _
      have tailBits := listCodeEncodeNat_length_mono tailCountBound
      have selectedSmall : selected.toNat ≤ 1 := by
        cases selected <;> simp
      have selectedBits :=
        listCodeEncodeNat_length_mono selectedSmall
      have selectedSpace :
          encodedListSpace [selected.toNat] ≤ budget := by
        have referenceBound :
            encodedListSpace [1, candidates.length] ≤ budget := by
          simp only [budget]
          omega
        simp only [encodedListSpace_cons, encodedListSpace_nil] at *
        omega
      have outputSpace :
          encodedListSpace [selected.toNat, tailCount] ≤ budget := by
        have referenceBound :
            encodedListSpace [1, candidates.length] ≤ budget := by
          simp only [budget]
          omega
        simp only [encodedListSpace_cons, encodedListSpace_nil] at *
        omega
      have argumentsBound := listCodePrependCost_le_of values
        [selected.toNat] [tailCount] headCost tailCost budget
        valuesBound selectedSpace outputSpace
      have argumentsBound' :
          prependCost values [selected.toNat] [tailCount]
              headCost tailCost ≤
            5 * budget + 2 := by
        omega
      have addition := natAddCost_le_linear selected.toNat tailCount
      have additionLimit :
          2 * (selected.toNat + tailCount) + 4 ≤
            2 * (candidates.length + 1) + 4 := by
        omega
      have additionBits :=
        listCodeEncodeNat_length_mono additionLimit
      have additionUnitBound :
          encodedListSpace
                [2 * (selected.toNat + tailCount) + 4] + 1 ≤
            budget := by
        have referenceBound :
            encodedListSpace
                [2 * (candidates.length + 1) + 4] + 1 ≤
              budget := by
          simp only [budget]
          omega
        simp only [encodedListSpace_cons, encodedListSpace_nil] at *
        omega
      have additionBound :
          natAddCost selected.toNat tailCount ≤
            100000000 * budget :=
        addition.trans (Nat.mul_le_mul_left _ additionUnitBound)
      change natAddCost selected.toNat tailCount +
          prependCost values [selected.toNat] [tailCount]
            headCost tailCost ≤ 200000000 * (budget + 1)
      omega

/-- Coefficient obtained by lifting the uniform quadratic candidate bound
through a compile-time candidate-count list. -/
def flatPackedCenterCoveringCandidateListCountQuadraticCoefficient :
    List (SquareSymmetry × Cell) → Nat
  | [] => 10000
  | _ :: candidates =>
      200000000 *
        (flatPackedCenterCoveringCandidateQuadraticCoefficient +
          flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
            candidates +
          (encodedListSpace [1, candidates.length] + 1) +
          (encodedListSpace [2 * (candidates.length + 1) + 4] + 1) + 102)

set_option maxRecDepth 100000 in
theorem flatPackedCenterCoveringCandidateListCountSpaceBound_le_quadratic
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall : ∀ candidate ∈ candidates,
      intOffsetAmount (-(candidate.1.act candidate.2).2) ≤ 4) :
    flatPackedCenterCoveringCandidateListCountSpaceBound tromino periodicStrip
        packed base candidates ≤
      flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
          candidates *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  have inputPositive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have inputQuadratic : input ≤ input ^ 2 := by nlinarith
  induction candidates with
  | nil =>
      simp [flatPackedCenterCoveringCandidateListCountSpaceBound,
        flatPackedCenterCoveringCandidateListCountQuadraticCoefficient]
      nlinarith
  | cons candidate candidates induction =>
      have headSmall := offsetSmall candidate (by simp)
      have tailSmall : ∀ remaining ∈ candidates,
          intOffsetAmount (-(remaining.1.act remaining.2).2) ≤ 4 := by
        intro remaining member
        exact offsetSmall remaining (by simp [member])
      have tail := induction tailSmall
      have head :=
        flatPackedCenterCoveringCandidateSpaceBound_le_quadratic
          candidate.1 candidate.2 periodicStrip packed base headSmall
      let firstExtra := encodedListSpace [1, candidates.length] + 1
      let secondExtra :=
        encodedListSpace [2 * (candidates.length + 1) + 4] + 1
      have constantsBound :
          firstExtra + secondExtra + 101 ≤
            (firstExtra + secondExtra + 101) * input ^ 2 := by
        have squarePositive : 1 ≤ input ^ 2 := by nlinarith
        simpa using Nat.mul_le_mul_left
          (firstExtra + secondExtra + 101) squarePositive
      have sumBound :
          flatPackedCenterCoveringCandidateSpaceBound candidate.1 candidate.2
                periodicStrip packed base +
              flatPackedCenterCoveringCandidateListCountSpaceBound tromino
                periodicStrip packed base candidates + input +
              firstExtra + secondExtra + 100 + 1 ≤
            (flatPackedCenterCoveringCandidateQuadraticCoefficient +
              flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
                candidates + firstExtra + secondExtra + 102) * input ^ 2 := by
        simp only [input] at head tail ⊢
        calc
          _ ≤ flatPackedCenterCoveringCandidateQuadraticCoefficient * input ^ 2 +
                flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
                  candidates * input ^ 2 + input + firstExtra + secondExtra +
                100 + 1 := by
            dsimp only [input]
            omega
          _ ≤ flatPackedCenterCoveringCandidateQuadraticCoefficient * input ^ 2 +
                flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
                  candidates * input ^ 2 + input ^ 2 +
                (firstExtra + secondExtra + 101) * input ^ 2 := by
            omega
          _ = (flatPackedCenterCoveringCandidateQuadraticCoefficient +
                flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
                  candidates + firstExtra + secondExtra + 102) * input ^ 2 := by
            ring
      change
        200000000 *
            (flatPackedCenterCoveringCandidateSpaceBound
                candidate.1 candidate.2 periodicStrip packed base +
              flatPackedCenterCoveringCandidateListCountSpaceBound tromino
                periodicStrip packed base candidates + input +
              firstExtra + secondExtra + 100 + 1) ≤
          flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
            (candidate :: candidates) * input ^ 2
      calc
        _ ≤ 200000000 *
              ((flatPackedCenterCoveringCandidateQuadraticCoefficient +
                flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
                  candidates + firstExtra + secondExtra + 102) * input ^ 2) :=
          Nat.mul_le_mul_left _ sumBound
        _ = (200000000 *
              (flatPackedCenterCoveringCandidateQuadraticCoefficient +
                flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
                  candidates + firstExtra + secondExtra + 102)) * input ^ 2 :=
          (Nat.mul_assoc _ _ _).symm
        _ = _ := rfl

def flatPackedCenterCoveringCountCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterCoveringCandidateListCountCost tromino
    periodicStrip packed base
    (Code.packedCenterCoveringCandidateList tromino)

def flatPackedCenterCoveringCountSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterCoveringCandidateListCountSpaceBound tromino
    periodicStrip packed base
    (Code.packedCenterCoveringCandidateList tromino)

def flatPackedCenterCoveringCountQuadraticCoefficient
    (tromino : Tromino) : Nat :=
  flatPackedCenterCoveringCandidateListCountQuadraticCoefficient
    (Code.packedCenterCoveringCandidateList tromino)

theorem flatPackedCenterCoveringCandidateList_offset_small
    (tromino : Tromino) (candidate : SquareSymmetry × Cell)
    (member : candidate ∈ Code.packedCenterCoveringCandidateList tromino) :
    intOffsetAmount (-(candidate.1.act candidate.2).2) ≤ 4 := by
  rcases candidate with ⟨symmetry, source⟩
  have sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino := by
    have pairMember :
        symmetry ∈ TrominoAssignment.squareSymmetryList ∧
          source ∈ TrominoAssignment.trominoCellList tromino := by
      simpa [Code.packedCenterCoveringCandidateList] using member
    exact pairMember.2
  cases tromino <;> cases symmetry <;>
    simp [TrominoAssignment.trominoCellList] at sourceMember
  all_goals rcases sourceMember with rfl | rfl | rfl <;> native_decide

theorem flatPackedCenterCoveringCountSpaceBound_le_quadratic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCoveringCountSpaceBound tromino periodicStrip packed base ≤
      flatPackedCenterCoveringCountQuadraticCoefficient tromino *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  apply flatPackedCenterCoveringCandidateListCountSpaceBound_le_quadratic
  intro candidate member
  exact flatPackedCenterCoveringCandidateList_offset_small
    tromino candidate member

theorem flatPackedCenterCoveringCountCost_le_bound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCoveringCountCost tromino periodicStrip packed base ≤
      flatPackedCenterCoveringCountSpaceBound tromino
        periodicStrip packed base :=
  flatPackedCenterCoveringCandidateListCountCost_le_bound tromino
    (Code.packedCenterCoveringCandidateList tromino)
    periodicStrip packed base

theorem flatPackedCenterCoveringCount
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCoveringCountCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(packed.activePlacementList
        tromino periodicStrip base.2).length]
      (flatPackedCenterCoveringCountCost tromino
        periodicStrip packed base) := by
  have sourcesValid : ∀ candidate ∈
      Code.packedCenterCoveringCandidateList tromino,
      candidate.2 ∈ TrominoAssignment.trominoCellList tromino := by
    intro candidate candidateMember
    rcases candidate with ⟨symmetry, source⟩
    have pairMember :
        symmetry ∈ TrominoAssignment.squareSymmetryList ∧
          source ∈ TrominoAssignment.trominoCellList tromino := by
      simpa [Code.packedCenterCoveringCandidateList] using candidateMember
    exact pairMember.2
  have result := flatPackedCenterCoveringCandidateListCount
    tromino (Code.packedCenterCoveringCandidateList tromino)
    sourcesValid periodicStrip packed base
  rw [Code.packedCenterCoveringCandidateList_filter_length
    tromino periodicStrip packed base.2] at result
  simpa [Code.flatPackedCenterCoveringCountCode,
    flatPackedCenterCoveringCountCost] using result

theorem flatPackedCenterActivePlacementList_length_le
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packed.activePlacementList
      tromino periodicStrip base.2).length ≤ 24 := by
  have filtered := List.length_filter_le
    (fun candidate : SquareSymmetry × Cell =>
      packed.localAssignment periodicStrip
        (Cell.sub (0, base.2) (candidate.1.act candidate.2)) =
          some candidate.1)
    (Code.packedCenterCoveringCandidateList tromino)
  rw [Code.packedCenterCoveringCandidateList_filter_length
    tromino periodicStrip packed base.2] at filtered
  have candidateLength :
      (Code.packedCenterCoveringCandidateList tromino).length = 24 := by
    cases tromino <;> native_decide
  omega

def flatPackedCenterExactlyOneCoveringArgumentsCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values :=
    Code.flatPackedCenterCandidateInput periodicStrip packed base
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  prependCost values [count] [1]
    (flatPackedCenterCoveringCountCost tromino
      periodicStrip packed base)
    (numeralCost 1 values)

theorem flatPackedCenterExactlyOneCoveringArguments
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    let count := (packed.activePlacementList
      tromino periodicStrip base.2).length
    EvaluatorCodeFits
      (Code.flatPackedCenterExactlyOneCoveringArgumentsCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [count, 1]
      (flatPackedCenterExactlyOneCoveringArgumentsCost tromino
        periodicStrip packed base) := by
  simp only
  let values :=
    Code.flatPackedCenterCandidateInput periodicStrip packed base
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  simpa [Code.flatPackedCenterExactlyOneCoveringArgumentsCode,
    flatPackedCenterExactlyOneCoveringArgumentsCost,
    values, count] using prepend
      (flatPackedCenterCoveringCount tromino periodicStrip packed base)
      (numeral 1 values)

def flatPackedCenterExactlyOneCoveringCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  natEqCost count 1 +
    flatPackedCenterExactlyOneCoveringArgumentsCost tromino
      periodicStrip packed base

/-- Common workspace unit for the 24-candidate count, its two-field equality
adapter, and the final comparison with one. -/
def flatPackedCenterExactlyOneCoveringSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedCenterCoveringCountSpaceBound tromino
      periodicStrip packed base +
    1000000 *
      flatPackedCenterCandidateInputUnit periodicStrip packed base +
    (encodedListSpace [24, 1] + 1) +
    (encodedListSpace [54] + 1) + 100

def flatPackedCenterExactlyOneCoveringSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  20000000000 *
    (flatPackedCenterExactlyOneCoveringSpaceUnit tromino
      periodicStrip packed base + 1)

set_option maxHeartbeats 800000 in
theorem flatPackedCenterExactlyOneCoveringCost_le_bound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterExactlyOneCoveringCost tromino
        periodicStrip packed base ≤
      flatPackedCenterExactlyOneCoveringSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.flatPackedCenterCandidateInput periodicStrip packed base
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  let countCost := flatPackedCenterCoveringCountCost tromino
    periodicStrip packed base
  let unit := flatPackedCenterExactlyOneCoveringSpaceUnit tromino
    periodicStrip packed base
  have unitLarge : 100 ≤ unit := by
    simp only [unit, flatPackedCenterExactlyOneCoveringSpaceUnit]
    omega
  have countBound : count ≤ 24 := by
    simpa [count] using flatPackedCenterActivePlacementList_length_le
      tromino periodicStrip packed base
  have countBits := listCodeEncodeNat_length_mono countBound
  have valuesBound : encodedListSpace values ≤ unit := by
    simp only [unit, flatPackedCenterExactlyOneCoveringSpaceUnit,
      flatPackedCenterCandidateInputUnit, values]
    omega
  have countCostBound : countCost ≤ unit := by
    have bound := flatPackedCenterCoveringCountCost_le_bound
      tromino periodicStrip packed base
    simp only [countCost, unit,
      flatPackedCenterExactlyOneCoveringSpaceUnit]
    omega
  have zeroBound := listCodeZeroCost_le_linear values
  have numeralAddSmall : addConstCost 1 [0] ≤ 100000 := by
    native_decide
  have numeralBound : numeralCost 1 values ≤ unit := by
    simp only [numeralCost]
    simp only [unit, flatPackedCenterExactlyOneCoveringSpaceUnit,
      flatPackedCenterCandidateInputUnit, values] at *
    omega
  have countSpace : encodedListSpace [count] ≤ unit := by
    have referenceBound : encodedListSpace [24, 1] ≤ unit := by
      simp only [unit, flatPackedCenterExactlyOneCoveringSpaceUnit]
      omega
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have outputSpace : encodedListSpace [count, 1] ≤ unit := by
    have referenceBound : encodedListSpace [24, 1] ≤ unit := by
      simp only [unit, flatPackedCenterExactlyOneCoveringSpaceUnit]
      omega
    have oneBits :
        (Computability.encodeNat 1).length = 1 := rfl
    simp only [encodedListSpace_cons, encodedListSpace_nil,
      oneBits] at *
    omega
  have argumentsRaw := listCodePrependCost_le_of values
    [count] [1] countCost (numeralCost 1 values) unit
    valuesBound countSpace outputSpace
  have argumentsBound :
      flatPackedCenterExactlyOneCoveringArgumentsCost tromino
          periodicStrip packed base ≤ 5 * unit + 2 := by
    change prependCost values [count] [1] countCost
        (numeralCost 1 values) ≤ 5 * unit + 2
    exact argumentsRaw.trans (by omega)
  have equality := natEqCost_le_linear count 1
  have equalityLimit : 2 * (count + 1) + 4 ≤ 54 := by omega
  have equalityBits := listCodeEncodeNat_length_mono equalityLimit
  have equalityUnit :
      encodedListSpace [2 * (count + 1) + 4] + 1 ≤ unit := by
    have referenceBound : encodedListSpace [54] + 1 ≤ unit := by
      simp only [unit, flatPackedCenterExactlyOneCoveringSpaceUnit]
      omega
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have equalityBound : natEqCost count 1 ≤
      10000000000 * unit :=
    equality.trans (Nat.mul_le_mul_left _ equalityUnit)
  change natEqCost count 1 +
      flatPackedCenterExactlyOneCoveringArgumentsCost tromino
        periodicStrip packed base ≤ 20000000000 * (unit + 1)
  omega

def flatPackedCenterExactlyOneCoveringQuadraticCoefficient
    (tromino : Tromino) : Nat :=
  20000000000 *
    (flatPackedCenterCoveringCountQuadraticCoefficient tromino + 1000000 +
      (encodedListSpace [24, 1] + 1) +
      (encodedListSpace [54] + 1) + 101)

set_option maxRecDepth 100000 in
theorem flatPackedCenterExactlyOneCoveringSpaceBound_le_quadratic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterExactlyOneCoveringSpaceBound tromino
        periodicStrip packed base ≤
      flatPackedCenterExactlyOneCoveringQuadraticCoefficient tromino *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2 := by
  let input := flatPackedCenterCandidateInputUnit periodicStrip packed base
  let firstExtra := encodedListSpace [24, 1] + 1
  let secondExtra := encodedListSpace [54] + 1
  have inputPositive : 1 ≤ input := by
    simp [input, flatPackedCenterCandidateInputUnit]
  have inputQuadratic : input ≤ input ^ 2 := by nlinarith
  have squarePositive : 1 ≤ input ^ 2 := by nlinarith
  have count := flatPackedCenterCoveringCountSpaceBound_le_quadratic
    tromino periodicStrip packed base
  have constantsBound :
      firstExtra + secondExtra + 101 ≤
        (firstExtra + secondExtra + 101) * input ^ 2 := by
    simpa using Nat.mul_le_mul_left
      (firstExtra + secondExtra + 101) squarePositive
  have sumBound :
      flatPackedCenterCoveringCountSpaceBound tromino periodicStrip packed base +
          1000000 * input + firstExtra + secondExtra + 100 + 1 ≤
        (flatPackedCenterCoveringCountQuadraticCoefficient tromino + 1000000 +
          firstExtra + secondExtra + 101) * input ^ 2 := by
    simp only [input] at count ⊢
    calc
      _ ≤ flatPackedCenterCoveringCountQuadraticCoefficient tromino * input ^ 2 +
            1000000 * input + firstExtra + secondExtra + 100 + 1 := by
        dsimp only [input]
        omega
      _ ≤ flatPackedCenterCoveringCountQuadraticCoefficient tromino * input ^ 2 +
            1000000 * input ^ 2 +
            (firstExtra + secondExtra + 101) * input ^ 2 := by
        omega
      _ = (flatPackedCenterCoveringCountQuadraticCoefficient tromino +
            1000000 + firstExtra + secondExtra + 101) * input ^ 2 := by
        ring
  change
    20000000000 *
        (flatPackedCenterCoveringCountSpaceBound tromino periodicStrip packed base +
          1000000 * input + firstExtra + secondExtra + 100 + 1) ≤
      flatPackedCenterExactlyOneCoveringQuadraticCoefficient tromino * input ^ 2
  calc
    _ ≤ 20000000000 *
          ((flatPackedCenterCoveringCountQuadraticCoefficient tromino +
            1000000 + firstExtra + secondExtra + 101) * input ^ 2) :=
      Nat.mul_le_mul_left _ sumBound
    _ = (20000000000 *
          (flatPackedCenterCoveringCountQuadraticCoefficient tromino +
            1000000 + firstExtra + secondExtra + 101)) * input ^ 2 :=
      (Nat.mul_assoc _ _ _).symm
    _ = _ := rfl

/-- Exact fitted execution of the 24-candidate exact-one coverage test. -/
theorem flatPackedCenterExactlyOneCovering
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterExactlyOneCoveringCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(decide ((packed.activePlacementList
        tromino periodicStrip base.2).length = 1)).toNat]
      (flatPackedCenterExactlyOneCoveringCost tromino
        periodicStrip packed base) := by
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  have result := comp (natEq count 1)
    (flatPackedCenterExactlyOneCoveringArguments
      tromino periodicStrip packed base)
  change EvaluatorCodeFits
    (Code.natEqCode.comp
      (Code.flatPackedCenterExactlyOneCoveringArgumentsCode tromino))
    (Code.flatPackedCenterCandidateInput periodicStrip packed base)
    [(decide (count = 1)).toNat]
    (natEqCost count 1 +
      flatPackedCenterExactlyOneCoveringArgumentsCost tromino
        periodicStrip packed base)
  have tagEq :
      (decide (count = 1)).toNat =
        if count = 1 then 1 else 0 := by
    by_cases exactOne : count = 1 <;> simp [exactOne]
  rw [tagEq]
  exact result

theorem flatPackedCenterExactlyOneCoveringPolynomialBounded
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterExactlyOneCoveringCode tromino)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(decide ((packed.activePlacementList
        tromino periodicStrip base.2).length = 1)).toNat]
      (flatPackedCenterExactlyOneCoveringQuadraticCoefficient tromino *
        (flatPackedCenterCandidateInputUnit periodicStrip packed base) ^ 2) :=
  (flatPackedCenterExactlyOneCovering tromino periodicStrip packed base).mono
    ((flatPackedCenterExactlyOneCoveringCost_le_bound tromino periodicStrip
      packed base).trans
        (flatPackedCenterExactlyOneCoveringSpaceBound_le_quadratic tromino
          periodicStrip packed base))

end EvaluatorCodeFits

end PartrecToTM2
end Turing

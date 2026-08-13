/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecPackedCenterCoverage
import LeanTrominoes.PartrecPackedCenterCoveringCandidateSpace

/-!
# Evaluator-space certificate for exact-one packed center coverage

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
def packedCenterCoveringCandidateListCountCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List (SquareSymmetry × Cell) -> Nat
  | [] => zeroCost
      (Code.packedCenterCandidateInput periodicStrip packed base)
  | candidate :: candidates =>
      let values :=
        Code.packedCenterCandidateInput periodicStrip packed base
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
        (packedCenterCoveringCandidateCost
          candidate.1 candidate.2 periodicStrip packed base)
        (packedCenterCoveringCandidateListCountCost
          tromino periodicStrip packed base candidates)
      natAddCost selected.toNat tailCount + argumentsCost

theorem packedCenterCoveringCandidateListCount
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (sourcesValid : ∀ candidate ∈ candidates,
      candidate.2 ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterCoveringCandidateListCountCode candidates)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(candidates.filter fun candidate =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (candidate.1.act candidate.2)) =
          some candidate.1).length]
      (packedCenterCoveringCandidateListCountCost tromino
        periodicStrip packed base candidates) := by
  induction candidates with
  | nil =>
      simpa [Code.packedCenterCoveringCandidateListCountCode,
        packedCenterCoveringCandidateListCountCost] using
        zero (Code.packedCenterCandidateInput
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
        Code.packedCenterCandidateInput periodicStrip packed base
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
      let headCost := packedCenterCoveringCandidateCost
        candidate.1 candidate.2 periodicStrip packed base
      let tailCost := packedCenterCoveringCandidateListCountCost
        tromino periodicStrip packed base candidates
      let argumentsCost := prependCost values [selectedBit.toNat]
        [tailCount] headCost tailCost
      have headFit :
          EvaluatorCodeFits
            (Code.packedCenterCoveringCandidateCode
              candidate.1 candidate.2)
            values [selectedBit.toNat] headCost := by
        simpa [values, selected, selectedBit, headCost] using
          packedCenterCoveringCandidate tromino
            candidate.1 candidate.2 sourceMember
            periodicStrip packed base
      have tailFit :
          EvaluatorCodeFits
            (Code.packedCenterCoveringCandidateListCountCode candidates)
            values [tailCount] tailCost := by
        simpa [values, tailCount, tailCost] using induction tailValid
      have argumentsFit :
          EvaluatorCodeFits
            (Code.prepend
              (Code.packedCenterCoveringCandidateCode
                candidate.1 candidate.2)
              (Code.packedCenterCoveringCandidateListCountCode candidates))
            values [selectedBit.toNat, tailCount]
            argumentsCost := by
        simpa [argumentsCost] using prepend headFit tailFit
      have result := comp (natAdd selectedBit.toNat tailCount)
        argumentsFit
      change EvaluatorCodeFits
        (Code.natAddCode.comp
          (Code.prepend
            (Code.packedCenterCoveringCandidateCode
              candidate.1 candidate.2)
            (Code.packedCenterCoveringCandidateListCountCode candidates)))
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
def packedCenterCoveringCandidateListCountSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    List (SquareSymmetry × Cell) → Nat
  | [] =>
      10000 *
        packedCenterCandidateInputUnit periodicStrip packed base
  | candidate :: candidates =>
      let budget :=
        packedCenterCoveringCandidateSpaceBound
            candidate.1 candidate.2 periodicStrip packed base +
          packedCenterCoveringCandidateListCountSpaceBound tromino
            periodicStrip packed base candidates +
          packedCenterCandidateInputUnit periodicStrip packed base +
          (encodedListSpace [1, candidates.length] + 1) +
          (encodedListSpace
            [2 * (candidates.length + 1) + 4] + 1) + 100
      200000000 * (budget + 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem packedCenterCoveringCandidateListCountCost_le_linear
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterCoveringCandidateListCountCost tromino
        periodicStrip packed base candidates ≤
      packedCenterCoveringCandidateListCountSpaceBound tromino
        periodicStrip packed base candidates := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  induction candidates with
  | nil =>
      simpa [packedCenterCoveringCandidateListCountCost,
        packedCenterCoveringCandidateListCountSpaceBound,
        packedCenterCandidateInputUnit, values] using
        listCodeZeroCost_le_linear values
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
      let headCost := packedCenterCoveringCandidateCost
        candidate.1 candidate.2 periodicStrip packed base
      let tailCost := packedCenterCoveringCandidateListCountCost
        tromino periodicStrip packed base candidates
      let budget :=
        packedCenterCoveringCandidateSpaceBound
            candidate.1 candidate.2 periodicStrip packed base +
          packedCenterCoveringCandidateListCountSpaceBound tromino
            periodicStrip packed base candidates +
          packedCenterCandidateInputUnit periodicStrip packed base +
          (encodedListSpace [1, candidates.length] + 1) +
          (encodedListSpace
            [2 * (candidates.length + 1) + 4] + 1) + 100
      have budgetLarge : 100 ≤ budget := by
        simp only [budget]
        omega
      have valuesBound : encodedListSpace values ≤ budget := by
        simp only [budget, packedCenterCandidateInputUnit, values]
        omega
      have headCostBound : headCost ≤ budget := by
        have bound := packedCenterCoveringCandidateCost_le_linear
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

/-- Coefficient obtained by lifting the uniform covering-candidate bound
through a fixed candidate-count list. -/
def packedCenterCoveringCandidateListCountLinearCoefficient :
    List (SquareSymmetry × Cell) → Nat
  | [] => 10000
  | _ :: candidates =>
      200000000 *
        (packedCenterCoveringCandidateLinearCoefficient +
          packedCenterCoveringCandidateListCountLinearCoefficient candidates +
          (encodedListSpace [1, candidates.length] + 1) +
          (encodedListSpace [2 * (candidates.length + 1) + 4] + 1) + 102)

set_option maxRecDepth 100000 in
theorem packedCenterCoveringCandidateListCountSpaceBound_le_input
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall : ∀ candidate ∈ candidates,
      intOffsetAmount (-(candidate.1.act candidate.2).2) ≤ 4) :
    packedCenterCoveringCandidateListCountSpaceBound tromino periodicStrip
        packed base candidates ≤
      packedCenterCoveringCandidateListCountLinearCoefficient candidates *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let input := packedCenterCandidateInputUnit periodicStrip packed base
  have inputPositive : 1 ≤ input := by
    simp [input, packedCenterCandidateInputUnit]
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      have headSmall := offsetSmall candidate (by simp)
      have tailSmall : ∀ remaining ∈ candidates,
          intOffsetAmount (-(remaining.1.act remaining.2).2) ≤ 4 := by
        intro remaining member
        exact offsetSmall remaining (by simp [member])
      have tail := induction tailSmall
      have head := packedCenterCoveringCandidateSpaceBound_le_input
        candidate.1 candidate.2 periodicStrip packed base headSmall
      let firstExtra := encodedListSpace [1, candidates.length] + 1
      let secondExtra :=
        encodedListSpace [2 * (candidates.length + 1) + 4] + 1
      have constantsBound :
          firstExtra + secondExtra + 101 ≤
            (firstExtra + secondExtra + 101) * input :=
        by simpa using
          Nat.mul_le_mul_left (firstExtra + secondExtra + 101) inputPositive
      have sumBound :
          packedCenterCoveringCandidateSpaceBound candidate.1 candidate.2
                periodicStrip packed base +
              packedCenterCoveringCandidateListCountSpaceBound tromino
                periodicStrip packed base candidates + input +
              firstExtra + secondExtra + 100 + 1 ≤
            (packedCenterCoveringCandidateLinearCoefficient +
              packedCenterCoveringCandidateListCountLinearCoefficient
                candidates + firstExtra + secondExtra + 102) * input := by
        simp only [input] at head tail ⊢
        calc
          _ ≤ packedCenterCoveringCandidateLinearCoefficient * input +
                packedCenterCoveringCandidateListCountLinearCoefficient
                  candidates * input + input + firstExtra + secondExtra +
                100 + 1 := by
            dsimp only [input]
            omega
          _ = (packedCenterCoveringCandidateLinearCoefficient +
                packedCenterCoveringCandidateListCountLinearCoefficient
                  candidates + 1) * input +
              (firstExtra + secondExtra + 101) := by ring
          _ ≤ (packedCenterCoveringCandidateLinearCoefficient +
                packedCenterCoveringCandidateListCountLinearCoefficient
                  candidates + 1) * input +
              (firstExtra + secondExtra + 101) * input :=
            Nat.add_le_add_left constantsBound _
          _ = (packedCenterCoveringCandidateLinearCoefficient +
                packedCenterCoveringCandidateListCountLinearCoefficient
                  candidates + firstExtra + secondExtra + 102) * input := by
            ring
      change
        200000000 *
            (packedCenterCoveringCandidateSpaceBound
                candidate.1 candidate.2 periodicStrip packed base +
              packedCenterCoveringCandidateListCountSpaceBound tromino
                periodicStrip packed base candidates + input +
              firstExtra + secondExtra + 100 + 1) ≤
          packedCenterCoveringCandidateListCountLinearCoefficient
            (candidate :: candidates) * input
      calc
        _ ≤ 200000000 *
              ((packedCenterCoveringCandidateLinearCoefficient +
                packedCenterCoveringCandidateListCountLinearCoefficient
                  candidates + firstExtra + secondExtra + 102) * input) :=
          Nat.mul_le_mul_left _ sumBound
        _ = (200000000 *
              (packedCenterCoveringCandidateLinearCoefficient +
                packedCenterCoveringCandidateListCountLinearCoefficient
                  candidates + firstExtra + secondExtra + 102)) * input :=
          (Nat.mul_assoc _ _ _).symm
        _ = _ := rfl

def packedCenterCoveringCountCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterCoveringCandidateListCountCost tromino
    periodicStrip packed base
    (Code.packedCenterCoveringCandidateList tromino)

def packedCenterCoveringCountSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterCoveringCandidateListCountSpaceBound tromino
    periodicStrip packed base
    (Code.packedCenterCoveringCandidateList tromino)

def packedCenterCoveringCountLinearCoefficient (tromino : Tromino) : Nat :=
  packedCenterCoveringCandidateListCountLinearCoefficient
    (Code.packedCenterCoveringCandidateList tromino)

theorem packedCenterCoveringCandidateList_offset_small
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

theorem packedCenterCoveringCountSpaceBound_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterCoveringCountSpaceBound tromino periodicStrip packed base ≤
      packedCenterCoveringCountLinearCoefficient tromino *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  apply packedCenterCoveringCandidateListCountSpaceBound_le_input
  intro candidate member
  exact packedCenterCoveringCandidateList_offset_small
    tromino candidate member

theorem packedCenterCoveringCountCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterCoveringCountCost tromino periodicStrip packed base ≤
      packedCenterCoveringCountSpaceBound tromino
        periodicStrip packed base :=
  packedCenterCoveringCandidateListCountCost_le_linear tromino
    (Code.packedCenterCoveringCandidateList tromino)
    periodicStrip packed base

theorem packedCenterCoveringCount
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterCoveringCountCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(packed.activePlacementList
        tromino periodicStrip base.2).length]
      (packedCenterCoveringCountCost tromino
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
  have result := packedCenterCoveringCandidateListCount
    tromino (Code.packedCenterCoveringCandidateList tromino)
    sourcesValid periodicStrip packed base
  rw [Code.packedCenterCoveringCandidateList_filter_length
    tromino periodicStrip packed base.2] at result
  simpa [Code.packedCenterCoveringCountCode,
    packedCenterCoveringCountCost] using result

theorem packedCenterActivePlacementList_length_le
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

def packedCenterExactlyOneCoveringArgumentsCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let values :=
    Code.packedCenterCandidateInput periodicStrip packed base
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  prependCost values [count] [1]
    (packedCenterCoveringCountCost tromino
      periodicStrip packed base)
    (numeralCost 1 values)

theorem packedCenterExactlyOneCoveringArguments
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    let count := (packed.activePlacementList
      tromino periodicStrip base.2).length
    EvaluatorCodeFits
      (Code.packedCenterExactlyOneCoveringArgumentsCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [count, 1]
      (packedCenterExactlyOneCoveringArgumentsCost tromino
        periodicStrip packed base) := by
  simp only
  let values :=
    Code.packedCenterCandidateInput periodicStrip packed base
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  simpa [Code.packedCenterExactlyOneCoveringArgumentsCode,
    packedCenterExactlyOneCoveringArgumentsCost,
    values, count] using prepend
      (packedCenterCoveringCount tromino periodicStrip packed base)
      (numeral 1 values)

def packedCenterExactlyOneCoveringCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  natEqCost count 1 +
    packedCenterExactlyOneCoveringArgumentsCost tromino
      periodicStrip packed base

/-- Common workspace unit for the 24-candidate count, its two-field equality
adapter, and the final comparison with one. -/
def packedCenterExactlyOneCoveringSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterCoveringCountSpaceBound tromino
      periodicStrip packed base +
    1000000 *
      packedCenterCandidateInputUnit periodicStrip packed base +
    (encodedListSpace [24, 1] + 1) +
    (encodedListSpace [54] + 1) + 100

def packedCenterExactlyOneCoveringSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  20000000000 *
    (packedCenterExactlyOneCoveringSpaceUnit tromino
      periodicStrip packed base + 1)

set_option maxHeartbeats 800000 in
theorem packedCenterExactlyOneCoveringCost_le_linear
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterExactlyOneCoveringCost tromino
        periodicStrip packed base ≤
      packedCenterExactlyOneCoveringSpaceBound tromino
        periodicStrip packed base := by
  let values := Code.packedCenterCandidateInput periodicStrip packed base
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  let countCost := packedCenterCoveringCountCost tromino
    periodicStrip packed base
  let unit := packedCenterExactlyOneCoveringSpaceUnit tromino
    periodicStrip packed base
  have unitLarge : 100 ≤ unit := by
    simp only [unit, packedCenterExactlyOneCoveringSpaceUnit]
    omega
  have countBound : count ≤ 24 := by
    simpa [count] using packedCenterActivePlacementList_length_le
      tromino periodicStrip packed base
  have countBits := listCodeEncodeNat_length_mono countBound
  have valuesBound : encodedListSpace values ≤ unit := by
    simp only [unit, packedCenterExactlyOneCoveringSpaceUnit,
      packedCenterCandidateInputUnit, values]
    omega
  have countCostBound : countCost ≤ unit := by
    have bound := packedCenterCoveringCountCost_le_linear
      tromino periodicStrip packed base
    simp only [countCost, unit,
      packedCenterExactlyOneCoveringSpaceUnit]
    omega
  have zeroBound := listCodeZeroCost_le_linear values
  have numeralAddSmall : addConstCost 1 [0] ≤ 100000 := by
    native_decide
  have numeralBound : numeralCost 1 values ≤ unit := by
    simp only [numeralCost]
    simp only [unit, packedCenterExactlyOneCoveringSpaceUnit,
      packedCenterCandidateInputUnit, values] at *
    omega
  have countSpace : encodedListSpace [count] ≤ unit := by
    have referenceBound : encodedListSpace [24, 1] ≤ unit := by
      simp only [unit, packedCenterExactlyOneCoveringSpaceUnit]
      omega
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have outputSpace : encodedListSpace [count, 1] ≤ unit := by
    have referenceBound : encodedListSpace [24, 1] ≤ unit := by
      simp only [unit, packedCenterExactlyOneCoveringSpaceUnit]
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
      packedCenterExactlyOneCoveringArgumentsCost tromino
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
      simp only [unit, packedCenterExactlyOneCoveringSpaceUnit]
      omega
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have equalityBound : natEqCost count 1 ≤
      10000000000 * unit :=
    equality.trans (Nat.mul_le_mul_left _ equalityUnit)
  change natEqCost count 1 +
      packedCenterExactlyOneCoveringArgumentsCost tromino
        periodicStrip packed base ≤ 20000000000 * (unit + 1)
  omega

def packedCenterExactlyOneCoveringLinearCoefficient
    (tromino : Tromino) : Nat :=
  20000000000 *
    (packedCenterCoveringCountLinearCoefficient tromino + 1000000 +
      (encodedListSpace [24, 1] + 1) +
      (encodedListSpace [54] + 1) + 101)

set_option maxRecDepth 100000 in
theorem packedCenterExactlyOneCoveringSpaceBound_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterExactlyOneCoveringSpaceBound tromino
        periodicStrip packed base ≤
      packedCenterExactlyOneCoveringLinearCoefficient tromino *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let input := packedCenterCandidateInputUnit periodicStrip packed base
  let firstExtra := encodedListSpace [24, 1] + 1
  let secondExtra := encodedListSpace [54] + 1
  have inputPositive : 1 ≤ input := by
    simp [input, packedCenterCandidateInputUnit]
  have count := packedCenterCoveringCountSpaceBound_le_input
    tromino periodicStrip packed base
  have constantsBound :
      firstExtra + secondExtra + 101 ≤
        (firstExtra + secondExtra + 101) * input := by
    simpa using Nat.mul_le_mul_left
      (firstExtra + secondExtra + 101) inputPositive
  have sumBound :
      packedCenterCoveringCountSpaceBound tromino periodicStrip packed base +
          1000000 * input + firstExtra + secondExtra + 100 + 1 ≤
        (packedCenterCoveringCountLinearCoefficient tromino + 1000000 +
          firstExtra + secondExtra + 101) * input := by
    simp only [input] at count ⊢
    calc
      _ ≤ packedCenterCoveringCountLinearCoefficient tromino * input +
            1000000 * input + firstExtra + secondExtra + 100 + 1 := by
        dsimp only [input]
        omega
      _ = (packedCenterCoveringCountLinearCoefficient tromino + 1000000) *
            input + (firstExtra + secondExtra + 101) := by ring
      _ ≤ (packedCenterCoveringCountLinearCoefficient tromino + 1000000) *
            input + (firstExtra + secondExtra + 101) * input :=
        Nat.add_le_add_left constantsBound _
      _ = (packedCenterCoveringCountLinearCoefficient tromino + 1000000 +
            firstExtra + secondExtra + 101) * input := by ring
  change
    20000000000 *
        (packedCenterCoveringCountSpaceBound tromino periodicStrip packed base +
          1000000 * input + firstExtra + secondExtra + 100 + 1) ≤
      packedCenterExactlyOneCoveringLinearCoefficient tromino * input
  calc
    _ ≤ 20000000000 *
          ((packedCenterCoveringCountLinearCoefficient tromino + 1000000 +
            firstExtra + secondExtra + 101) * input) :=
      Nat.mul_le_mul_left _ sumBound
    _ = (20000000000 *
          (packedCenterCoveringCountLinearCoefficient tromino + 1000000 +
            firstExtra + secondExtra + 101)) * input :=
      (Nat.mul_assoc _ _ _).symm
    _ = _ := rfl

/-- Exact fitted execution of the 24-candidate exact-one coverage test. -/
theorem packedCenterExactlyOneCovering
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterExactlyOneCoveringCode tromino)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(decide ((packed.activePlacementList
        tromino periodicStrip base.2).length = 1)).toNat]
      (packedCenterExactlyOneCoveringCost tromino
        periodicStrip packed base) := by
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  have result := comp (natEq count 1)
    (packedCenterExactlyOneCoveringArguments
      tromino periodicStrip packed base)
  change EvaluatorCodeFits
    (Code.natEqCode.comp
      (Code.packedCenterExactlyOneCoveringArgumentsCode tromino))
    (Code.packedCenterCandidateInput periodicStrip packed base)
    [(decide (count = 1)).toNat]
    (natEqCost count 1 +
      packedCenterExactlyOneCoveringArgumentsCost tromino
        periodicStrip packed base)
  have tagEq :
      (decide (count = 1)).toNat =
        if count = 1 then 1 else 0 := by
    by_cases exactOne : count = 1 <;> simp [exactOne]
  rw [tagEq]
  exact result

end EvaluatorCodeFits

end PartrecToTM2
end Turing

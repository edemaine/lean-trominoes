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

def packedCenterCoveringCountCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedCenterCoveringCandidateListCountCost tromino
    periodicStrip packed base
    (Code.packedCenterCoveringCandidateList tromino)

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

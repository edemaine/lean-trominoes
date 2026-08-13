/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecAdd
import LeanTrominoes.PartrecPackedCenterCoveringCandidate

/-!
# Exact-one packed center coverage

There are exactly 24 possible placements covering a center target: eight
square symmetries times three source cells.  This file sums the corresponding
fixed active-candidate bits, proves that the sum is the semantic filtered-list
length, and compares the result with one.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- The fixed symmetry/source enumeration underlying center coverage. -/
def packedCenterCoveringCandidateList
    (tromino : Tromino) : List (SquareSymmetry × Cell) :=
  TrominoAssignment.squareSymmetryList.product
    (TrominoAssignment.trominoCellList tromino)

/-- Sum the active bits for a fixed list of symmetry/source candidates. -/
def packedCenterCoveringCandidateListCountCode :
    List (SquareSymmetry × Cell) -> Code
  | [] => zero
  | candidate :: candidates =>
      natAddCode.comp <|
        prepend
          (packedCenterCoveringCandidateCode
            candidate.1 candidate.2)
          (packedCenterCoveringCandidateListCountCode candidates)

theorem packedCenterCoveringCandidateListCountCode_eval
    (tromino : Tromino)
    (candidates : List (SquareSymmetry × Cell))
    (sourcesValid : ∀ candidate ∈ candidates,
      candidate.2 ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterCoveringCandidateListCountCode candidates).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(candidates.filter fun candidate =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (candidate.1.act candidate.2)) =
          some candidate.1).length] := by
  induction candidates with
  | nil =>
      simp [packedCenterCoveringCandidateListCountCode]
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
      let selected : Prop :=
        packed.localAssignment periodicStrip
            (Cell.sub (0, base.2)
              (candidate.1.act candidate.2)) =
          some candidate.1
      let tailCount := (candidates.filter fun remaining =>
        packed.localAssignment periodicStrip
          (Cell.sub (0, base.2)
            (remaining.1.act remaining.2)) =
          some remaining.1).length
      have headRun :
          (packedCenterCoveringCandidateCode
              candidate.1 candidate.2).eval
              (packedCenterCandidateInput
                periodicStrip packed base) =
            pure [(decide selected).toNat] := by
        simpa [selected] using
          packedCenterCoveringCandidateCode_eval_semantic
            tromino candidate.1 candidate.2 sourceMember
            periodicStrip packed base
      have tailRun :
          (packedCenterCoveringCandidateListCountCode candidates).eval
              (packedCenterCandidateInput
                periodicStrip packed base) =
            pure [tailCount] := by
        simpa [tailCount] using induction tailValid
      have arguments :
          (prepend
            (packedCenterCoveringCandidateCode
              candidate.1 candidate.2)
            (packedCenterCoveringCandidateListCountCode candidates)).eval
              (packedCenterCandidateInput
                periodicStrip packed base) =
            pure [(decide selected).toNat, tailCount] := by
        simp [headRun, tailRun]
      have added := natAddCode_eval (decide selected).toNat tailCount
      have run :
          (packedCenterCoveringCandidateListCountCode
              (candidate :: candidates)).eval
              (packedCenterCandidateInput
                periodicStrip packed base) =
            pure [(decide selected).toNat + tailCount] := by
        simpa [packedCenterCoveringCandidateListCountCode] using
          (comp_eval_pure _ _ _ _ arguments).trans added
      by_cases selectedProof : selected
      · have selectedTrue : decide selected = true := by simp [selectedProof]
        have headTrue :
            decide
              (packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (candidate.1.act candidate.2)) =
                some candidate.1) = true := by
          simpa [selected] using selectedTrue
        have countEq :
            ((candidate :: candidates).filter fun remaining =>
              packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (remaining.1.act remaining.2)) =
                some remaining.1).length = 1 + tailCount := by
          simp only [List.filter_cons, headTrue, ↓reduceIte,
            List.length_cons]
          simp only [tailCount]
          omega
        rw [countEq]
        simpa [selectedTrue] using run
      · have selectedFalse : decide selected = false := by simp [selectedProof]
        have headFalse :
            decide
              (packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (candidate.1.act candidate.2)) =
                some candidate.1) = false := by
          simpa [selected] using selectedFalse
        have countEq :
            ((candidate :: candidates).filter fun remaining =>
              packed.localAssignment periodicStrip
                (Cell.sub (0, base.2)
                  (remaining.1.act remaining.2)) =
                some remaining.1).length = tailCount := by
          simp only [List.filter_cons, headFalse]
          rfl
        rw [countEq]
        simpa [selectedFalse] using run

/-- Count all active center-covering placements. -/
def packedCenterCoveringCountCode (tromino : Tromino) : Code :=
  packedCenterCoveringCandidateListCountCode
    (packedCenterCoveringCandidateList tromino)

/-- Filtering the candidate-pair list and filtering the mapped placement list
have the same length. -/
theorem packedCenterCoveringCandidateList_filter_length
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (row : Int) :
    ((packedCenterCoveringCandidateList tromino).filter fun candidate =>
      packed.localAssignment periodicStrip
        (Cell.sub (0, row) (candidate.1.act candidate.2)) =
          some candidate.1).length =
      (packed.activePlacementList
        tromino periodicStrip row).length := by
  let candidates := packedCenterCoveringCandidateList tromino
  let placement : SquareSymmetry × Cell -> Placement Unit :=
    fun candidate =>
      { kind := ()
        symmetry := candidate.1
        offset := Cell.sub (0, row)
          (candidate.1.act candidate.2) }
  let active : Placement Unit -> Prop := fun candidate =>
    packed.localAssignment periodicStrip candidate.offset =
      some candidate.symmetry
  have filteredMap :=
    (@List.filter_map (SquareSymmetry × Cell) (Placement Unit)
      placement active candidates).symm
  have lengths := congrArg List.length filteredMap
  simpa [PackedWindowState.activePlacementList,
    TrominoAssignment.coveringPlacementList,
    packedCenterCoveringCandidateList,
    candidates, placement, active, Function.comp_def] using lengths

@[simp]
theorem packedCenterCoveringCountCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterCoveringCountCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.activePlacementList
        tromino periodicStrip base.2).length] := by
  have sourcesValid : ∀ candidate ∈
      packedCenterCoveringCandidateList tromino,
      candidate.2 ∈ TrominoAssignment.trominoCellList tromino := by
    intro candidate candidateMember
    rcases candidate with ⟨symmetry, source⟩
    have pairMember :
        symmetry ∈ TrominoAssignment.squareSymmetryList ∧
          source ∈ TrominoAssignment.trominoCellList tromino := by
      simpa [packedCenterCoveringCandidateList] using candidateMember
    exact pairMember.2
  have counted := packedCenterCoveringCandidateListCountCode_eval
    tromino (packedCenterCoveringCandidateList tromino)
    sourcesValid periodicStrip packed base
  rw [packedCenterCoveringCandidateList_filter_length
    tromino periodicStrip packed base.2] at counted
  exact counted

/-- Assemble `[activeCoveringCount, 1]`. -/
def packedCenterExactlyOneCoveringArgumentsCode
    (tromino : Tromino) : Code :=
  prepend (packedCenterCoveringCountCode tromino) (numeral 1)

@[simp]
theorem packedCenterExactlyOneCoveringArgumentsCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterExactlyOneCoveringArgumentsCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.activePlacementList
          tromino periodicStrip base.2).length, 1] := by
  simp [packedCenterExactlyOneCoveringArgumentsCode]

/-- Decide whether exactly one placement covers the center target. -/
def packedCenterExactlyOneCoveringCode
    (tromino : Tromino) : Code :=
  natEqCode.comp
    (packedCenterExactlyOneCoveringArgumentsCode tromino)

/-- The explicit 24-candidate count computes the semantic exact-one coverage
condition at the center target. -/
@[simp]
theorem packedCenterExactlyOneCoveringCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterExactlyOneCoveringCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(decide ((packed.activePlacementList
        tromino periodicStrip base.2).length = 1)).toNat] := by
  let count := (packed.activePlacementList
    tromino periodicStrip base.2).length
  have arguments := packedCenterExactlyOneCoveringArgumentsCode_eval
    tromino periodicStrip packed base
  have compared := natEqCode_eval count 1
  have run :
      (packedCenterExactlyOneCoveringCode tromino).eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [if count = 1 then 1 else 0] := by
    simpa only [packedCenterExactlyOneCoveringCode] using
      (comp_eval_pure _ _ _ _ arguments).trans compared
  change
    (packedCenterExactlyOneCoveringCode tromino).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(decide (count = 1)).toNat]
  have tagEq :
      (decide (count = 1)).toNat =
        if count = 1 then 1 else 0 := by
    by_cases exactOne : count = 1 <;> simp [exactOne]
  rw [tagEq]
  exact run

end Turing.ToPartrec.Code

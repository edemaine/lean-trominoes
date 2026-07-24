import LeanTrominoes.PartrecPackedAssignmentLookup
import LeanTrominoes.StripFrontierPacked

/-!
# Five-column packed frontier lookup

The frontier word consists of five consecutive motif-sized blocks.  This file
unrolls those five columns around the fitted one-column scanner.  The live
state is

`[motifCode, queriedColumn, targetCellCode, word, digit, found]`.

Each stage compares the queried column with one fixed numeral, scans exactly
one motif block, and preserves a successful earlier lookup.  The final program
returns the assignment digit selected by the semantic `assignmentKeys` order.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input =
      outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Fixed-width state between the five unrolled column scans. -/
def packedAssignmentLookupState
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (accumulator : Nat × Nat × Bool) : List Nat :=
  [Encodable.encode motif, queriedColumn, Encodable.encode target,
    accumulator.1, accumulator.2.1, accumulator.2.2.toNat]

/-- Semantic update performed by one numbered column stage. -/
def packedAssignmentLookupApplyColumn
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) : Nat × Nat × Bool :=
  packedLookupColumnOutcome target
    (decide (queriedColumn = currentColumn)) motif
    accumulator.1 accumulator.2.1 accumulator.2.2

theorem packedAssignmentLookupApplyColumn_word_le
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupApplyColumn currentColumn motif
      queriedColumn target accumulator).1 ≤ accumulator.1 := by
  simpa [packedAssignmentLookupApplyColumn] using
    packedLookupColumnOutcome_word_le target
      (decide (queriedColumn = currentColumn)) motif
      accumulator.1 accumulator.2.1 accumulator.2.2

theorem packedAssignmentLookupApplyColumn_digit_le
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupApplyColumn currentColumn motif
      queriedColumn target accumulator).2.1 ≤
        accumulator.2.1 + 8 := by
  simpa [packedAssignmentLookupApplyColumn] using
    packedLookupColumnOutcome_digit_le target
      (decide (queriedColumn = currentColumn)) motif
      accumulator.1 accumulator.2.1 accumulator.2.2

/-- Arguments `[queriedColumn, currentColumn]` for the stage selector. -/
def packedAssignmentLookupColumnEqArgumentsCode
    (currentColumn : Nat) : Code :=
  prepend (get 1) (numeral currentColumn)

@[simp]
theorem packedAssignmentLookupColumnEqArgumentsCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupColumnEqArgumentsCode
      currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure [queriedColumn, currentColumn] := by
  simp [packedAssignmentLookupColumnEqArgumentsCode,
    packedAssignmentLookupState]

/-- Normalized selector for one numbered column. -/
def packedAssignmentLookupColumnSelectedCode
    (currentColumn : Nat) : Code :=
  natEqCode.comp
    (packedAssignmentLookupColumnEqArgumentsCode currentColumn)

@[simp]
theorem packedAssignmentLookupColumnSelectedCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupColumnSelectedCode currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure [(decide (queriedColumn = currentColumn)).toNat] := by
  by_cases equal : queriedColumn = currentColumn <;>
    simp [packedAssignmentLookupColumnSelectedCode,
      equal]

/-- Build the six-field input of the fitted one-column scanner. -/
def packedAssignmentLookupColumnInputCode
    (currentColumn : Nat) : Code :=
  prepend (get 0) <|
    prepend (get 2) <|
      prepend (get 3) <|
        prepend (get 4) <|
          prepend (get 5)
            (packedAssignmentLookupColumnSelectedCode currentColumn)

@[simp]
theorem packedAssignmentLookupColumnInputCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupColumnInputCode currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure
        [Encodable.encode motif, Encodable.encode target,
          accumulator.1, accumulator.2.1,
          accumulator.2.2.toNat,
          (decide (queriedColumn = currentColumn)).toNat] := by
  have selectedRun :=
    packedAssignmentLookupColumnSelectedCode_eval
      currentColumn motif queriedColumn target accumulator
  change
    (packedAssignmentLookupColumnInputCode currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure
        [Encodable.encode motif, Encodable.encode target,
          accumulator.1, accumulator.2.1,
          accumulator.2.2.toNat,
          (decide (queriedColumn = currentColumn)).toNat]
  simp [packedAssignmentLookupColumnInputCode, selectedRun]
  all_goals simp [packedAssignmentLookupState]

/-- Invoke one complete motif scan for the selected stage. -/
def packedAssignmentLookupColumnCallCode
    (currentColumn : Nat) : Code :=
  packedLookupColumnCode.comp
    (packedAssignmentLookupColumnInputCode currentColumn)

@[simp]
theorem packedAssignmentLookupColumnCallCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupColumnCallCode currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure
        (packedLookupColumnResult motif target
          accumulator.1 accumulator.2.1 accumulator.2.2
          (decide (queriedColumn = currentColumn))) := by
  exact comp_eval_pure _ _ _ _
    (packedAssignmentLookupColumnInputCode_eval
      currentColumn motif queriedColumn target accumulator) |>.trans
    (packedLookupColumnCode_eval motif target
      accumulator.1 accumulator.2.1 accumulator.2.2
      (decide (queriedColumn = currentColumn)))

/-- Select one accumulator field from the one-column result. -/
def packedAssignmentLookupColumnResultFieldCode
    (currentColumn outputField : Nat) : Code :=
  (get outputField).comp
    (packedAssignmentLookupColumnCallCode currentColumn)

@[simp]
theorem packedAssignmentLookupColumnResultFieldCode_eval
    (currentColumn outputField : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupColumnResultFieldCode
      currentColumn outputField).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure
        [(packedLookupColumnResult motif target
          accumulator.1 accumulator.2.1 accumulator.2.2
          (decide
            (queriedColumn = currentColumn)))[outputField]?.getD 0] := by
  simp [packedAssignmentLookupColumnResultFieldCode]

/-- One complete numbered stage, preserving the query around the scan. -/
def packedAssignmentLookupColumnStageCode
    (currentColumn : Nat) : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend
          (packedAssignmentLookupColumnResultFieldCode
            currentColumn 2) <|
          prepend
            (packedAssignmentLookupColumnResultFieldCode
              currentColumn 3)
            (packedAssignmentLookupColumnResultFieldCode
              currentColumn 4)

@[simp]
theorem packedAssignmentLookupColumnStageCode_eval
    (currentColumn : Nat) (motif : List Cell)
    (queriedColumn : Nat) (target : Cell)
    (accumulator : Nat × Nat × Bool) :
    (packedAssignmentLookupColumnStageCode currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure
        (packedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupApplyColumn currentColumn motif
            queriedColumn target accumulator)) := by
  have wordRun :=
    packedAssignmentLookupColumnResultFieldCode_eval
      currentColumn 2 motif queriedColumn target accumulator
  have digitRun :=
    packedAssignmentLookupColumnResultFieldCode_eval
      currentColumn 3 motif queriedColumn target accumulator
  have foundRun :=
    packedAssignmentLookupColumnResultFieldCode_eval
      currentColumn 4 motif queriedColumn target accumulator
  change
    (packedAssignmentLookupColumnStageCode currentColumn).eval
        (packedAssignmentLookupState motif queriedColumn
          target accumulator) =
      pure
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target,
          (packedAssignmentLookupApplyColumn currentColumn motif
            queriedColumn target accumulator).1,
          (packedAssignmentLookupApplyColumn currentColumn motif
            queriedColumn target accumulator).2.1,
          (packedAssignmentLookupApplyColumn currentColumn motif
            queriedColumn target accumulator).2.2.toNat]
  simp [packedAssignmentLookupColumnStageCode,
    packedAssignmentLookupApplyColumn,
    packedLookupColumnResult_eq_outcome,
    wordRun, digitRun, foundRun]
  all_goals simp [packedAssignmentLookupState]

/-- Apply columns zero through four in assignment-key order. -/
def packedAssignmentLookupOutcome
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat × Nat × Bool :=
  let first :=
    packedAssignmentLookupApplyColumn 0 motif queriedColumn target
      (word, 0, false)
  let second :=
    packedAssignmentLookupApplyColumn 1 motif queriedColumn target first
  let third :=
    packedAssignmentLookupApplyColumn 2 motif queriedColumn target second
  let fourth :=
    packedAssignmentLookupApplyColumn 3 motif queriedColumn target third
  packedAssignmentLookupApplyColumn 4 motif queriedColumn target fourth

theorem packedAssignmentLookupOutcome_word_le
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    (packedAssignmentLookupOutcome motif queriedColumn
      target word).1 ≤ word := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    packedAssignmentLookupApplyColumn 0 motif queriedColumn target initial
  let second :=
    packedAssignmentLookupApplyColumn 1 motif queriedColumn target first
  let third :=
    packedAssignmentLookupApplyColumn 2 motif queriedColumn target second
  let fourth :=
    packedAssignmentLookupApplyColumn 3 motif queriedColumn target third
  have firstLe :=
    packedAssignmentLookupApplyColumn_word_le
      0 motif queriedColumn target initial
  have secondLe :=
    packedAssignmentLookupApplyColumn_word_le
      1 motif queriedColumn target first
  have thirdLe :=
    packedAssignmentLookupApplyColumn_word_le
      2 motif queriedColumn target second
  have fourthLe :=
    packedAssignmentLookupApplyColumn_word_le
      3 motif queriedColumn target third
  have fifthLe :=
    packedAssignmentLookupApplyColumn_word_le
      4 motif queriedColumn target fourth
  simpa [packedAssignmentLookupOutcome,
    initial, first, second, third, fourth] using
    fifthLe.trans (fourthLe.trans
      (thirdLe.trans (secondLe.trans firstLe)))

theorem packedAssignmentLookupOutcome_digit_le
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    (packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1 ≤ 40 := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    packedAssignmentLookupApplyColumn 0 motif queriedColumn target initial
  let second :=
    packedAssignmentLookupApplyColumn 1 motif queriedColumn target first
  let third :=
    packedAssignmentLookupApplyColumn 2 motif queriedColumn target second
  let fourth :=
    packedAssignmentLookupApplyColumn 3 motif queriedColumn target third
  let fifth :=
    packedAssignmentLookupApplyColumn 4 motif queriedColumn target fourth
  have firstLe : first.2.1 ≤ initial.2.1 + 8 := by
    simpa [first] using
      packedAssignmentLookupApplyColumn_digit_le
        0 motif queriedColumn target initial
  have secondLe : second.2.1 ≤ first.2.1 + 8 := by
    simpa [second] using
      packedAssignmentLookupApplyColumn_digit_le
        1 motif queriedColumn target first
  have thirdLe : third.2.1 ≤ second.2.1 + 8 := by
    simpa [third] using
      packedAssignmentLookupApplyColumn_digit_le
        2 motif queriedColumn target second
  have fourthLe : fourth.2.1 ≤ third.2.1 + 8 := by
    simpa [fourth] using
      packedAssignmentLookupApplyColumn_digit_le
        3 motif queriedColumn target third
  have fifthLe : fifth.2.1 ≤ fourth.2.1 + 8 := by
    simpa [fifth] using
      packedAssignmentLookupApplyColumn_digit_le
        4 motif queriedColumn target fourth
  change fifth.2.1 ≤ 40
  simp only [initial] at firstLe
  omega

/-- Explicit composition of the five numbered stages. -/
def packedAssignmentLookupStagesCode : Code :=
  (packedAssignmentLookupColumnStageCode 4).comp <|
    (packedAssignmentLookupColumnStageCode 3).comp <|
      (packedAssignmentLookupColumnStageCode 2).comp <|
        (packedAssignmentLookupColumnStageCode 1).comp
          (packedAssignmentLookupColumnStageCode 0)

@[simp]
theorem packedAssignmentLookupStagesCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupStagesCode.eval
        (packedAssignmentLookupState motif queriedColumn target
          (word, 0, false)) =
      pure
        (packedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupOutcome motif queriedColumn
            target word)) := by
  let initial : Nat × Nat × Bool := (word, 0, false)
  let first :=
    packedAssignmentLookupApplyColumn 0 motif queriedColumn target
      initial
  let second :=
    packedAssignmentLookupApplyColumn 1 motif queriedColumn target first
  let third :=
    packedAssignmentLookupApplyColumn 2 motif queriedColumn target second
  let fourth :=
    packedAssignmentLookupApplyColumn 3 motif queriedColumn target third
  let fifth :=
    packedAssignmentLookupApplyColumn 4 motif queriedColumn target fourth
  have run0 :=
    packedAssignmentLookupColumnStageCode_eval
      0 motif queriedColumn target initial
  have run1 :=
    packedAssignmentLookupColumnStageCode_eval
      1 motif queriedColumn target first
  have run2 :=
    packedAssignmentLookupColumnStageCode_eval
      2 motif queriedColumn target second
  have run3 :=
    packedAssignmentLookupColumnStageCode_eval
      3 motif queriedColumn target third
  have run4 :=
    packedAssignmentLookupColumnStageCode_eval
      4 motif queriedColumn target fourth
  have run01 :
      ((packedAssignmentLookupColumnStageCode 1).comp
          (packedAssignmentLookupColumnStageCode 0)).eval
          (packedAssignmentLookupState motif queriedColumn target
            initial) =
        pure
          (packedAssignmentLookupState motif queriedColumn target
            second) := by
    calc
      _ = (packedAssignmentLookupColumnStageCode 1).eval
          (packedAssignmentLookupState motif queriedColumn target
            first) :=
        comp_eval_pure _ _ _ _ run0
      _ = pure
          (packedAssignmentLookupState motif queriedColumn target
            second) := run1
  have run012 :
      ((packedAssignmentLookupColumnStageCode 2).comp
          ((packedAssignmentLookupColumnStageCode 1).comp
            (packedAssignmentLookupColumnStageCode 0))).eval
          (packedAssignmentLookupState motif queriedColumn target
            initial) =
        pure
          (packedAssignmentLookupState motif queriedColumn target
            third) := by
    calc
      _ = (packedAssignmentLookupColumnStageCode 2).eval
          (packedAssignmentLookupState motif queriedColumn target
            second) :=
        comp_eval_pure _ _ _ _ run01
      _ = pure
          (packedAssignmentLookupState motif queriedColumn target
            third) := run2
  have run0123 :
      ((packedAssignmentLookupColumnStageCode 3).comp
          ((packedAssignmentLookupColumnStageCode 2).comp
            ((packedAssignmentLookupColumnStageCode 1).comp
              (packedAssignmentLookupColumnStageCode 0)))).eval
          (packedAssignmentLookupState motif queriedColumn target
            initial) =
        pure
          (packedAssignmentLookupState motif queriedColumn target
            fourth) := by
    calc
      _ = (packedAssignmentLookupColumnStageCode 3).eval
          (packedAssignmentLookupState motif queriedColumn target
            third) :=
        comp_eval_pure _ _ _ _ run012
      _ = pure
          (packedAssignmentLookupState motif queriedColumn target
            fourth) := run3
  calc
    _ = (packedAssignmentLookupColumnStageCode 4).eval
        (packedAssignmentLookupState motif queriedColumn target fourth) :=
      comp_eval_pure _ _ _ _ run0123
    _ = pure
        (packedAssignmentLookupState motif queriedColumn target fifth) :=
      run4
    _ = pure
        (packedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupOutcome motif queriedColumn
            target word)) := by
      rfl

/-- Initialize the five-stage lookup from
`[motifCode, queriedColumn, targetCellCode, word]`. -/
def packedAssignmentLookupInputCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend zero zero

@[simp]
theorem packedAssignmentLookupInputCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupInputCode.eval
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target, word] =
      pure
        (packedAssignmentLookupState motif queriedColumn target
          (word, 0, false)) := by
  simp [packedAssignmentLookupInputCode,
    packedAssignmentLookupState]

/-- Complete lookup returning `[digit, found]`. -/
def packedAssignmentLookupCode : Code :=
  (prepend (get 4) (get 5)).comp <|
    packedAssignmentLookupStagesCode.comp
      packedAssignmentLookupInputCode

@[simp]
theorem packedAssignmentLookupCode_eval
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupCode.eval
        [Encodable.encode motif, queriedColumn,
          Encodable.encode target, word] =
      pure
        [(packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1,
          (packedAssignmentLookupOutcome motif queriedColumn
            target word).2.2.toNat] := by
  have stages :
      (packedAssignmentLookupStagesCode.comp
        packedAssignmentLookupInputCode).eval
          [Encodable.encode motif, queriedColumn,
            Encodable.encode target, word] =
        pure
          (packedAssignmentLookupState motif queriedColumn target
            (packedAssignmentLookupOutcome motif queriedColumn
              target word)) := by
    calc
      _ = packedAssignmentLookupStagesCode.eval
          (packedAssignmentLookupState motif queriedColumn target
            (word, 0, false)) :=
        comp_eval_pure _ _ _ _
          (packedAssignmentLookupInputCode_eval
            motif queriedColumn target word)
      _ = pure
          (packedAssignmentLookupState motif queriedColumn target
            (packedAssignmentLookupOutcome motif queriedColumn
              target word)) :=
        packedAssignmentLookupStagesCode_eval
          motif queriedColumn target word
  calc
    _ = (prepend (get 4) (get 5)).eval
        (packedAssignmentLookupState motif queriedColumn target
          (packedAssignmentLookupOutcome motif queriedColumn
            target word)) :=
      comp_eval_pure _ _ _ _ stages
    _ = pure
        [(packedAssignmentLookupOutcome motif queriedColumn
            target word).2.1,
          (packedAssignmentLookupOutcome motif queriedColumn
            target word).2.2.toNat] := by
      simp [packedAssignmentLookupState]

/-- Dividing by a base-nine block advances digit lookup by that block. -/
theorem assignmentDigitAt_div_pow
    (word offset position : Nat) :
    assignmentDigitAt (word / 9 ^ offset) position =
      assignmentDigitAt word (offset + position) := by
  unfold assignmentDigitAt
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Successful five-column lookup agrees with the canonical assignment-key
position. -/
theorem packedAssignmentLookupOutcome_digit_of_mem
    (motif : List Cell) (target : Cell) (word : Nat)
    (column : Fin 5) (member : target ∈ motif) :
    (packedAssignmentLookupOutcome motif column.val
        target word).2.1 =
      assignmentDigitAt word
        (column.val * motif.length +
          @List.idxOf Cell instBEqOfDecidableEq target motif) := by
  fin_cases column <;>
    simp [packedAssignmentLookupOutcome,
      packedAssignmentLookupApplyColumn,
      packedLookupColumnOutcome_selected_of_mem
        target motif _ _ member,
      assignmentDigitAt_div_pow,
      Nat.div_div_eq_div_mul, ← pow_add] <;>
    congr 2 <;> omega

theorem packedAssignmentLookupOutcome_found_of_mem
    (motif : List Cell) (target : Cell) (word : Nat)
    (column : Fin 5) (member : target ∈ motif) :
    (packedAssignmentLookupOutcome motif column.val
        target word).2.2 = true := by
  fin_cases column <;>
    simp [packedAssignmentLookupOutcome,
      packedAssignmentLookupApplyColumn,
      packedLookupColumnOutcome_selected_of_mem
        target motif _ _ member,
      Nat.div_div_eq_div_mul, ← pow_add]

theorem packedAssignmentLookupOutcome_of_not_mem
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat)
    (absent : target ∉ motif) :
    (packedAssignmentLookupOutcome motif queriedColumn
        target word).2 =
      (0, false) := by
  simp [packedAssignmentLookupOutcome,
    packedAssignmentLookupApplyColumn,
    packedLookupColumnOutcome_of_not_mem
      target _ motif _ _ absent,
    Nat.div_div_eq_div_mul, ← pow_add]

/-- Pairing every list entry with a fixed column preserves first-occurrence
indices. -/
theorem idxOf_pair_map
    (column : WindowColumn) (target : Cell)
    (motif : List Cell) :
    @List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
        (column, target)
        (motif.map fun cell => (column, cell)) =
      @List.idxOf Cell instBEqOfDecidableEq target motif := by
  letI : BEq (WindowColumn × Cell) := instBEqOfDecidableEq
  letI : BEq Cell := instBEqOfDecidableEq
  induction motif with
  | nil =>
      rfl
  | cons cell motif induction =>
      by_cases equal : cell = target
      · subst target
        simp
      · have pairNe :
          (column, cell) ≠ (column, target) := by
            intro pairEqual
            exact equal (Prod.mk.inj pairEqual).2
        simpa [List.idxOf_cons_ne motif equal,
          List.idxOf_cons_ne
            (motif.map fun item => (column, item)) pairNe] using
          congrArg Nat.succ induction

/-- Position of a present cell in the five-block assignment-key order. -/
theorem assignmentKeys_idxOf_eq
    (periodicStrip : PeriodicStrip)
    (column : WindowColumn) (target : Cell)
    (member : target ∈ periodicStrip.motif) :
    @List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
        (column, target) (assignmentKeys periodicStrip) =
      column.val * periodicStrip.motif.length +
        @List.idxOf Cell instBEqOfDecidableEq
          target periodicStrip.motif := by
  have columns :
      (List.finRange 5 : List (Fin 5)) =
        [0, 1, 2, 3, 4] := by
    native_decide
  rw [assignmentKeys, columns]
  fin_cases column <;>
    simp [motifCells, member, idxOf_pair_map,
      List.idxOf_append_of_mem,
      List.idxOf_append_of_notMem] <;>
    omega

theorem packedAssignmentLookupCode_eval_assignmentKeys
    (periodicStrip : PeriodicStrip)
    (column : WindowColumn) (target : Cell)
    (word : Nat) (member : target ∈ periodicStrip.motif) :
    packedAssignmentLookupCode.eval
        [Encodable.encode periodicStrip.motif, column.val,
          Encodable.encode target, word] =
      pure
        [assignmentDigitAt word
            (@List.idxOf (WindowColumn × Cell)
              instBEqOfDecidableEq (column, target)
              (assignmentKeys periodicStrip)),
          1] := by
  rw [packedAssignmentLookupCode_eval]
  rw [packedAssignmentLookupOutcome_digit_of_mem
    periodicStrip.motif target word column member]
  rw [packedAssignmentLookupOutcome_found_of_mem
    periodicStrip.motif target word column member]
  rw [assignmentKeys_idxOf_eq periodicStrip column target member]
  rfl

@[simp]
theorem assignmentOfDigit_zero :
    assignmentOfDigit 0 = none := by
  simp [assignmentOfDigit,
    TrominoAssignment.assignmentStateList]

/-- The five-column arithmetic lookup decodes to the semantic packed
assignment, including the absent-cell default. -/
theorem assignmentOfDigit_packedAssignmentLookupOutcome
    (periodicStrip : PeriodicStrip)
    (packed : PeriodicStrip.PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    assignmentOfDigit
        (packedAssignmentLookupOutcome periodicStrip.motif
          column.val target packed.assignmentWord).2.1 =
      packed.assignmentAtCell periodicStrip column target := by
  letI : BEq (WindowColumn × Cell) := instBEqOfDecidableEq
  by_cases member : target ∈ periodicStrip.motif
  · have keyMember :
        (column, target) ∈ assignmentKeys periodicStrip := by
      simp [assignmentKeys, motifCells, member]
    have positionBound :
        @List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
            (column, target) (assignmentKeys periodicStrip) <
          (assignmentKeys periodicStrip).length :=
      List.idxOf_lt_length_of_mem keyMember
    rw [packedAssignmentLookupOutcome_digit_of_mem
      periodicStrip.motif target packed.assignmentWord column member]
    rw [← assignmentKeys_idxOf_eq
      periodicStrip column target member]
    unfold PeriodicStrip.PackedWindowState.assignmentAtCell
      PeriodicStrip.PackedWindowState.assignmentPosition
    rw [if_pos positionBound]
  · have keyAbsent :
        (column, target) ∉ assignmentKeys periodicStrip := by
      simp [assignmentKeys, motifCells, member]
    have positionEq :
        @List.idxOf (WindowColumn × Cell) instBEqOfDecidableEq
            (column, target) (assignmentKeys periodicStrip) =
          (assignmentKeys periodicStrip).length :=
      List.idxOf_eq_length_iff.mpr keyAbsent
    have outcome :=
      packedAssignmentLookupOutcome_of_not_mem
        periodicStrip.motif column.val target
        packed.assignmentWord member
    have digitZero :
        (packedAssignmentLookupOutcome periodicStrip.motif
          column.val target packed.assignmentWord).2.1 = 0 := by
      exact congrArg Prod.fst outcome
    rw [digitZero, assignmentOfDigit_zero]
    unfold PeriodicStrip.PackedWindowState.assignmentAtCell
      PeriodicStrip.PackedWindowState.assignmentPosition
    rw [positionEq]
    simp

end Turing.ToPartrec.Code

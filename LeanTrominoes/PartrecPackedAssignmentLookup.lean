import LeanTrominoes.PartrecFrontierIndexDecode
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecStripWellFormed

/-!
# Streaming lookup in packed frontier assignments

A packed frontier stores all five motif-column assignments as the low digits
of one base-nine natural.  Looking up a particular `(column, cell)` must use
the first occurrence of `cell` in the motif, because the strip definition
does not require the motif list to be duplicate-free.

This module implements one column of that lookup.  The loop scans an encoded
motif suffix and peels one base-nine digit per cell.  Once it finds the first
matching cell in the selected column, it records the exposed digit and
freezes.  A nonselected column consumes its entire block without changing the
recorded result.  Empty and already-found states are fixed points, so the
encoded motif itself is a safe countdown.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes

attribute [local simp] Part.bind_eq_bind

/-- Reachable payload for one packed assignment-column scan.

The fields are remaining motif, original motif, target cell, residual packed
word, recorded digit, found tag, and selected-column tag. -/
def packedLookupColumnState
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) : List Nat :=
  [Encodable.encode remaining, Encodable.encode original,
    Encodable.encode target, word, digit, found.toNat, selected.toNat]

/-- Decode the remaining motif stored in field zero. -/
def packedLookupColumnViewCode : Code :=
  encodedListViewCode.comp (get 0)

/-- Encoded head cell of a nonempty remaining motif. -/
def packedLookupColumnHeadCode : Code :=
  (get 1).comp packedLookupColumnViewCode

/-- Encoded tail of a nonempty remaining motif. -/
def packedLookupColumnTailCode : Code :=
  (get 2).comp packedLookupColumnViewCode

@[simp]
theorem packedLookupColumnViewCode_eval
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    packedLookupColumnViewCode.eval
        (packedLookupColumnState original remaining target
          word digit found selected) =
      pure
        (match remaining with
        | [] => [0, 0, 0]
        | cell :: rest =>
            [1, Encodable.encode cell, Encodable.encode rest]) := by
  cases remaining with
  | nil =>
      calc
        _ = encodedListViewCode.eval [0] := by
          simp [packedLookupColumnViewCode,
            packedLookupColumnState]
        _ = pure [0, 0, 0] :=
          encodedListViewCode_eval ([] : List Cell)
  | cons cell remaining =>
      calc
        _ = encodedListViewCode.eval
            [Encodable.encode (cell :: remaining)] := by
          simp [packedLookupColumnViewCode,
            packedLookupColumnState]
        _ = pure
            [1, Encodable.encode cell,
              Encodable.encode remaining] :=
          encodedListViewCode_eval (cell :: remaining)

@[simp]
theorem packedLookupColumnHeadCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnHeadCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure [Encodable.encode cell] := by
  simp [packedLookupColumnHeadCode]

@[simp]
theorem packedLookupColumnTailCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnTailCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure [Encodable.encode remaining] := by
  simp [packedLookupColumnTailCode]

/-- Assemble the encoded head and target cells for natural equality. -/
def packedLookupColumnEqualityArgumentsCode : Code :=
  prepend packedLookupColumnHeadCode (get 2)

@[simp]
theorem packedLookupColumnEqualityArgumentsCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnEqualityArgumentsCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure [Encodable.encode cell, Encodable.encode target] := by
  have headEval :=
    packedLookupColumnHeadCode_eval original target cell remaining
      word digit found selected
  have targetEval :
      (get 2).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [Encodable.encode target] := by
    simp [packedLookupColumnState]
  simp [packedLookupColumnEqualityArgumentsCode,
    headEval, targetEval]

/-- True exactly when the current cell is in the selected column and equals
the target cell. -/
def packedLookupColumnMatchCode : Code :=
  boolAnd (get 6)
    (natEqCode.comp packedLookupColumnEqualityArgumentsCode)

@[simp]
theorem packedLookupColumnMatchCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnMatchCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure [(selected && decide (cell = target)).toNat] := by
  have equalityEval :
      (natEqCode.comp
        packedLookupColumnEqualityArgumentsCode).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [if cell = target then 1 else 0] := by
    by_cases equal : cell = target
    · subst target
      simp
    · have encodedNe :
          Encodable.encode cell ≠ Encodable.encode target := by
        intro encodedEqual
        exact equal (Encodable.encode_injective encodedEqual)
      simp [encodedNe, equal]
  have combined :=
    boolAnd_eval_at (get 6)
      (natEqCode.comp packedLookupColumnEqualityArgumentsCode)
      (packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      selected.toNat
      (if cell = target then 1 else 0)
      (by simp [packedLookupColumnState])
      equalityEval
  cases selected <;>
    by_cases equal : cell = target <;>
    simp [equal] at combined ⊢
  all_goals exact combined

/-- State update when the current cell is not the desired first occurrence. -/
def packedLookupColumnContinueCode : Code :=
  prepend packedLookupColumnTailCode <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (assignmentWordStepFieldAtCode 3 0) <|
          prepend (get 4) <|
            prepend (get 5) (get 6)

@[simp]
theorem packedLookupColumnContinueCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnContinueCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure
        (packedLookupColumnState original remaining target
          (word / 9) digit found selected) := by
  have tailEval :=
    packedLookupColumnTailCode_eval original target cell remaining
      word digit found selected
  have originalEval :
      (get 1).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [Encodable.encode original] := by
    simp [packedLookupColumnState]
  have targetEval :
      (get 2).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [Encodable.encode target] := by
    simp [packedLookupColumnState]
  have wordTailEval :
      (assignmentWordStepFieldAtCode 3 0).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [word / 9] := by
    simp [packedLookupColumnState]
  have digitEval :
      (get 4).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [digit] := by
    simp [packedLookupColumnState]
  have foundEval :
      (get 5).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [found.toNat] := by
    simp [packedLookupColumnState]
  have selectedEval :
      (get 6).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [selected.toNat] := by
    simp [packedLookupColumnState]
  change
    packedLookupColumnContinueCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure
        [Encodable.encode remaining, Encodable.encode original,
          Encodable.encode target, word / 9, digit,
          found.toNat, selected.toNat]
  simp [packedLookupColumnContinueCode,
    tailEval, originalEval, targetEval, wordTailEval,
    digitEval, foundEval, selectedEval]

/-- State update at the desired first occurrence: record the exposed digit
and set the found tag. -/
def packedLookupColumnFoundCode : Code :=
  prepend packedLookupColumnTailCode <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (assignmentWordStepFieldAtCode 3 0) <|
          prepend (assignmentWordStepFieldAtCode 3 1) <|
            prepend one (get 6)

@[simp]
theorem packedLookupColumnFoundCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnFoundCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure
        (packedLookupColumnState original remaining target
          (word / 9) (word % 9) true selected) := by
  have tailEval :=
    packedLookupColumnTailCode_eval original target cell remaining
      word digit found selected
  have originalEval :
      (get 1).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [Encodable.encode original] := by
    simp [packedLookupColumnState]
  have targetEval :
      (get 2).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [Encodable.encode target] := by
    simp [packedLookupColumnState]
  have wordTailEval :
      (assignmentWordStepFieldAtCode 3 0).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [word / 9] := by
    simp [packedLookupColumnState]
  have wordDigitEval :
      (assignmentWordStepFieldAtCode 3 1).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [word % 9] := by
    simp [packedLookupColumnState]
  have selectedEval :
      (get 6).eval
          (packedLookupColumnState original (cell :: remaining)
            target word digit found selected) =
        pure [selected.toNat] := by
    simp [packedLookupColumnState]
  change
    packedLookupColumnFoundCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit found selected) =
      pure
        [Encodable.encode remaining, Encodable.encode original,
          Encodable.encode target, word / 9, word % 9, 1,
          selected.toNat]
  simp [packedLookupColumnFoundCode,
    tailEval, originalEval, targetEval, wordTailEval,
    wordDigitEval, selectedEval]

/-- Nonempty, not-yet-found step. -/
def packedLookupColumnConsStepCode : Code :=
  branchZero packedLookupColumnMatchCode
    packedLookupColumnContinueCode
    packedLookupColumnFoundCode

@[simp]
theorem packedLookupColumnConsStepCode_eval
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (selected : Bool) :
    packedLookupColumnConsStepCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit false selected) =
      pure
        (if selected && decide (cell = target) then
          packedLookupColumnState original remaining target
            (word / 9) (word % 9) true selected
        else
          packedLookupColumnState original remaining target
            (word / 9) digit false selected) := by
  by_cases hit : selected && decide (cell = target)
  · rw [if_pos hit]
    exact
      branchZero_eval_succ_at packedLookupColumnMatchCode
        packedLookupColumnContinueCode packedLookupColumnFoundCode
        (packedLookupColumnState original (cell :: remaining)
          target word digit false selected)
        (selected && decide (cell = target)).toNat
        (packedLookupColumnMatchCode_eval
          original target cell remaining word digit false selected)
        (packedLookupColumnState original remaining target
          (word / 9) (word % 9) true selected)
        (packedLookupColumnFoundCode_eval
          original target cell remaining word digit false selected)
        (by simp [hit])
  · rw [if_neg hit]
    exact
      branchZero_eval_zero_at packedLookupColumnMatchCode
        packedLookupColumnContinueCode packedLookupColumnFoundCode
        (packedLookupColumnState original (cell :: remaining)
          target word digit false selected)
        (selected && decide (cell = target)).toNat
        (packedLookupColumnMatchCode_eval
          original target cell remaining word digit false selected)
        (packedLookupColumnState original remaining target
          (word / 9) digit false selected)
        (packedLookupColumnContinueCode_eval
          original target cell remaining word digit false selected)
        (by simp [hit])

/-- One total scan step.  Empty and already-found states are fixed points. -/
def packedLookupColumnStepCode : Code :=
  branchZero (get 5)
    (branchZero (get 0) id packedLookupColumnConsStepCode)
    id

@[simp]
theorem packedLookupColumnStepCode_eval_found
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) :
    packedLookupColumnStepCode.eval
        (packedLookupColumnState original remaining target
          word digit true selected) =
      pure
        (packedLookupColumnState original remaining target
          word digit true selected) := by
  exact
    branchZero_eval_succ_at (get 5)
      (branchZero (get 0) id packedLookupColumnConsStepCode) id
      (packedLookupColumnState original remaining target
        word digit true selected)
      1 (by simp [packedLookupColumnState])
      (packedLookupColumnState original remaining target
        word digit true selected)
      (by simp) (by omega)

@[simp]
theorem packedLookupColumnStepCode_eval_nil
    (original : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) :
    packedLookupColumnStepCode.eval
        (packedLookupColumnState original [] target
          word digit false selected) =
      pure
        (packedLookupColumnState original [] target
          word digit false selected) := by
  apply branchZero_eval_zero_at (get 5)
      (branchZero (get 0) id packedLookupColumnConsStepCode) id
      (packedLookupColumnState original [] target
        word digit false selected)
      0 (by simp [packedLookupColumnState])
      (packedLookupColumnState original [] target
        word digit false selected)
  · exact
      branchZero_eval_zero_at (get 0) id
        packedLookupColumnConsStepCode
        (packedLookupColumnState original [] target
          word digit false selected)
        0 (by simp [packedLookupColumnState])
        (packedLookupColumnState original [] target
          word digit false selected)
        (by simp) rfl
  · rfl

@[simp]
theorem packedLookupColumnStepCode_eval_cons
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (selected : Bool) :
    packedLookupColumnStepCode.eval
        (packedLookupColumnState original (cell :: remaining)
          target word digit false selected) =
      pure
        (if selected && decide (cell = target) then
          packedLookupColumnState original remaining target
            (word / 9) (word % 9) true selected
        else
          packedLookupColumnState original remaining target
            (word / 9) digit false selected) := by
  apply branchZero_eval_zero_at (get 5)
      (branchZero (get 0) id packedLookupColumnConsStepCode) id
      (packedLookupColumnState original (cell :: remaining)
        target word digit false selected)
      0 (by simp [packedLookupColumnState])
      (if selected && decide (cell = target) then
        packedLookupColumnState original remaining target
          (word / 9) (word % 9) true selected
      else
        packedLookupColumnState original remaining target
          (word / 9) digit false selected)
  · exact
      branchZero_eval_succ_at (get 0) id
        packedLookupColumnConsStepCode
        (packedLookupColumnState original (cell :: remaining)
          target word digit false selected)
        (Encodable.encode (cell :: remaining))
        (by simp [packedLookupColumnState])
        (if selected && decide (cell = target) then
          packedLookupColumnState original remaining target
            (word / 9) (word % 9) true selected
        else
          packedLookupColumnState original remaining target
            (word / 9) digit false selected)
        (packedLookupColumnConsStepCode_eval
          original target cell remaining word digit selected)
        (by simp)
  · rfl

/-- Typed semantics of exactly `steps` packed column iterations. -/
def packedLookupColumnProcess
    (original : List Cell) (target : Cell) :
    Nat → List Cell → Nat → Nat → Bool → Bool → List Nat
  | 0, remaining, word, digit, found, selected =>
      packedLookupColumnState original remaining target
        word digit found selected
  | steps + 1, remaining, word, digit, true, selected =>
      packedLookupColumnProcess original target steps remaining
        word digit true selected
  | steps + 1, [], word, digit, false, selected =>
      packedLookupColumnProcess original target steps []
        word digit false selected
  | steps + 1, cell :: remaining, word, digit, false, selected =>
      if selected && decide (cell = target) then
        packedLookupColumnProcess original target steps remaining
          (word / 9) (word % 9) true selected
      else
        packedLookupColumnProcess original target steps remaining
          (word / 9) digit false selected

theorem packedLookupColumnFlatIterateCode_eval
    (original remaining : List Cell) (target : Cell)
    (steps word digit : Nat) (found selected : Bool) :
    (flatIterate packedLookupColumnStepCode).eval
        (steps ::
          packedLookupColumnState original remaining target
            word digit found selected) =
      pure
        (packedLookupColumnProcess original target steps remaining
          word digit found selected) := by
  rw [flatIterate, fix_eval]
  apply Part.eq_some_iff.mpr
  induction steps generalizing remaining word digit found with
  | zero =>
      apply PFun.mem_fix_iff.mpr
      left
      simp [flatCountdownBody_zero_eval,
        packedLookupColumnProcess]
  | succ steps induction =>
      apply PFun.mem_fix_iff.mpr
      right
      cases found with
      | true =>
          refine
            ⟨steps ::
                packedLookupColumnState original remaining target
                  word digit true selected,
              ?_, ?_⟩
          · simp [flatCountdownBody,
              packedLookupColumnStepCode_eval_found]
          · simpa [packedLookupColumnProcess] using
              induction remaining word digit true
      | false =>
          cases remaining with
          | nil =>
              refine
                ⟨steps ::
                    packedLookupColumnState original [] target
                      word digit false selected,
                  ?_, ?_⟩
              · simp [flatCountdownBody,
                  packedLookupColumnStepCode_eval_nil]
              · simpa [packedLookupColumnProcess] using
                  induction [] word digit false
          | cons cell remaining =>
              by_cases hit :
                  selected && decide (cell = target)
              · refine
                  ⟨steps ::
                      packedLookupColumnState original remaining target
                        (word / 9) (word % 9) true selected,
                    ?_, ?_⟩
                · simp [flatCountdownBody,
                    packedLookupColumnStepCode_eval_cons, hit]
                · simpa [packedLookupColumnProcess, hit] using
                    induction remaining (word / 9) (word % 9) true
              · refine
                  ⟨steps ::
                      packedLookupColumnState original remaining target
                        (word / 9) digit false selected,
                    ?_, ?_⟩
                · simp [flatCountdownBody,
                    packedLookupColumnStepCode_eval_cons, hit]
                · simpa [packedLookupColumnProcess, hit] using
                    induction remaining (word / 9) digit false

/-- Closed recursive result of scanning until the motif is exhausted or the
first selected occurrence is found. -/
def packedLookupColumnScanState
    (original : List Cell) (target : Cell) :
    List Cell → Nat → Nat → Bool → Bool → List Nat
  | remaining, word, digit, true, selected =>
      packedLookupColumnState original remaining target
        word digit true selected
  | [], word, digit, false, selected =>
      packedLookupColumnState original [] target
        word digit false selected
  | cell :: remaining, word, digit, false, selected =>
      if selected && decide (cell = target) then
        packedLookupColumnState original remaining target
          (word / 9) (word % 9) true selected
      else
        packedLookupColumnScanState original target remaining
          (word / 9) digit false selected

@[simp]
theorem packedLookupColumnProcess_found
    (original remaining : List Cell) (target : Cell)
    (steps word digit : Nat) (selected : Bool) :
    packedLookupColumnProcess original target steps remaining
        word digit true selected =
      packedLookupColumnState original remaining target
        word digit true selected := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      simpa [packedLookupColumnProcess] using induction

@[simp]
theorem packedLookupColumnProcess_nil
    (original : List Cell) (target : Cell)
    (steps word digit : Nat) (selected : Bool) :
    packedLookupColumnProcess original target steps []
        word digit false selected =
      packedLookupColumnState original [] target
        word digit false selected := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      simpa [packedLookupColumnProcess] using induction

/-- Any countdown at least as long as the motif reaches the closed scan
result.  In particular, the motif encoding is a safe countdown. -/
theorem packedLookupColumnProcess_of_length_le
    (original remaining : List Cell) (target : Cell)
    (steps word digit : Nat) (found selected : Bool)
    (enough : remaining.length ≤ steps) :
    packedLookupColumnProcess original target steps remaining
        word digit found selected =
      packedLookupColumnScanState original target remaining
        word digit found selected := by
  cases found with
  | true =>
      simp [packedLookupColumnScanState]
  | false =>
      induction remaining generalizing steps word digit with
      | nil =>
          simp [packedLookupColumnScanState]
      | cons cell remaining induction =>
          cases steps with
          | zero =>
              simp at enough
          | succ steps =>
              have remainingEnough :
                  remaining.length ≤ steps := by
                simpa using enough
              by_cases hit :
                  selected && decide (cell = target)
              · simp [packedLookupColumnProcess,
                  packedLookupColumnScanState, hit]
              · rw [packedLookupColumnProcess,
                  packedLookupColumnScanState, if_neg hit]
                simpa [hit] using
                  induction steps (word / 9) digit
                    remainingEnough

theorem packedLookupColumnProcess_encode
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    packedLookupColumnProcess motif target
        (Encodable.encode motif) motif word digit found selected =
      packedLookupColumnScanState motif target motif
        word digit found selected := by
  exact packedLookupColumnProcess_of_length_le
    motif motif target (Encodable.encode motif)
    word digit found selected (length_le_encode motif)

/-- Peeling one low base-nine digit advances `assignmentDigitAt` by one
position. -/
theorem assignmentDigitAt_div_nine
    (word position : Nat) :
    LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt
        (word / 9) position =
      LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt
        word (position + 1) := by
  unfold
    LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt
  rw [pow_succ, Nat.div_div_eq_div_mul]
  congr 2
  omega

/-- In a selected column, a successful scan records the digit at the target's
first motif occurrence. -/
theorem packedLookupColumnScanState_digit_of_mem
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (member : target ∈ remaining) :
    (packedLookupColumnScanState original target remaining
        word digit false true)[4]?.getD 0 =
      LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt
        word
        (@List.idxOf Cell instBEqOfDecidableEq target remaining) := by
  induction remaining generalizing word with
  | nil =>
      simp at member
  | cons cell remaining induction =>
      by_cases equal : cell = target
      · subst target
        simp [packedLookupColumnScanState,
          packedLookupColumnState,
          LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt]
      · have tailMember : target ∈ remaining := by
          have targetNe : target ≠ cell := Ne.symm equal
          simpa [targetNe] using member
        rw [packedLookupColumnScanState, if_neg (by simp [equal])]
        rw [induction (word / 9) tailMember]
        rw [assignmentDigitAt_div_nine]
        simp [equal]

/-- A target present in the selected column sets the found tag. -/
theorem packedLookupColumnScanState_found_of_mem
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (member : target ∈ remaining) :
    (packedLookupColumnScanState original target remaining
        word digit false true)[5]?.getD 0 = 1 := by
  induction remaining generalizing word with
  | nil =>
      simp at member
  | cons cell remaining induction =>
      by_cases equal : cell = target
      · subst target
        simp [packedLookupColumnScanState,
          packedLookupColumnState]
      · have tailMember : target ∈ remaining := by
          have targetNe : target ≠ cell := Ne.symm equal
          simpa [targetNe] using member
        rw [packedLookupColumnScanState, if_neg (by simp [equal])]
        exact induction (word / 9) tailMember

/-- An absent target leaves the recorded digit and found tag unchanged. -/
theorem packedLookupColumnScanState_of_not_mem
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool)
    (absent : target ∉ remaining) :
    (packedLookupColumnScanState original target remaining
        word digit false selected)[4]?.getD 0 = digit ∧
      (packedLookupColumnScanState original target remaining
        word digit false selected)[5]?.getD 0 = 0 := by
  induction remaining generalizing word with
  | nil =>
      simp [packedLookupColumnScanState,
        packedLookupColumnState]
  | cons cell remaining induction =>
      have unequal : cell ≠ target := by
        intro equal
        apply absent
        simp [equal]
      have tailAbsent : target ∉ remaining := by
        intro member
        exact absent (by simp [member])
      rw [packedLookupColumnScanState, if_neg (by simp [unequal])]
      exact induction (word / 9) tailAbsent

/-- A nonselected column can only skip its complete motif-sized digit block;
it cannot alter an earlier lookup result. -/
theorem packedLookupColumnScanState_not_selected
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found : Bool) :
    (packedLookupColumnScanState original target remaining
        word digit found false)[4]?.getD 0 = digit ∧
      (packedLookupColumnScanState original target remaining
        word digit found false)[5]?.getD 0 = found.toNat := by
  cases found with
  | true =>
      simp [packedLookupColumnScanState,
        packedLookupColumnState]
  | false =>
      by_cases member : target ∈ remaining
      · induction remaining generalizing word with
        | nil =>
            simp at member
        | cons cell remaining induction =>
            rw [packedLookupColumnScanState, if_neg (by simp)]
            by_cases tailMember : target ∈ remaining
            · exact induction (word / 9) tailMember
            · exact packedLookupColumnScanState_of_not_mem
                original remaining target (word / 9) digit false
                tailMember
      · exact packedLookupColumnScanState_of_not_mem
          original remaining target word digit false member

end Turing.ToPartrec.Code

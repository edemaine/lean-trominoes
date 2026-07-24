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

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input =
      outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

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

/-- Total native-list semantics used by the reachable-state space rule.  Only
typed encoded motif states are reachable in the fitted loop. -/
def packedLookupColumnNativeStep (values : List Nat) : List Nat :=
  if values[5]?.getD 0 ≠ 0 then values
  else
    match decodeCellList values.headI with
    | none => values
    | some [] => values
    | some (cell :: remaining) =>
        if values[6]?.getD 0 ≠ 0 ∧
            Encodable.encode cell = values[2]?.getD 0 then
          [Encodable.encode remaining,
            values[1]?.getD 0, values[2]?.getD 0,
            values[3]?.getD 0 / 9,
            values[3]?.getD 0 % 9, 1,
            values[6]?.getD 0]
        else
          [Encodable.encode remaining,
            values[1]?.getD 0, values[2]?.getD 0,
            values[3]?.getD 0 / 9,
            values[4]?.getD 0, values[5]?.getD 0,
            values[6]?.getD 0]

@[simp]
theorem packedLookupColumnNativeStep_state_found
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) :
    packedLookupColumnNativeStep
        (packedLookupColumnState original remaining target
          word digit true selected) =
      packedLookupColumnState original remaining target
        word digit true selected := by
  simp [packedLookupColumnNativeStep,
    packedLookupColumnState]

@[simp]
theorem packedLookupColumnNativeStep_state_nil
    (original : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) :
    packedLookupColumnNativeStep
        (packedLookupColumnState original [] target
          word digit false selected) =
      packedLookupColumnState original [] target
        word digit false selected := by
  simp [packedLookupColumnNativeStep,
    packedLookupColumnState]

@[simp]
theorem packedLookupColumnNativeStep_state_cons
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (selected : Bool) :
    packedLookupColumnNativeStep
        (packedLookupColumnState original (cell :: remaining)
          target word digit false selected) =
      if selected && decide (cell = target) then
        packedLookupColumnState original remaining target
          (word / 9) (word % 9) true selected
      else
        packedLookupColumnState original remaining target
          (word / 9) digit false selected := by
  cases selected <;>
    by_cases equal : cell = target <;>
    simp [packedLookupColumnNativeStep,
      packedLookupColumnState, equal]

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

theorem packedLookupColumnNativeStep_iterate
    (original remaining : List Cell) (target : Cell)
    (steps word digit : Nat) (found selected : Bool) :
    ((packedLookupColumnNativeStep)^[steps])
        (packedLookupColumnState original remaining target
          word digit found selected) =
      packedLookupColumnProcess original target steps remaining
        word digit found selected := by
  induction steps generalizing remaining word digit found with
  | zero =>
      rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      cases found with
      | true =>
          rw [packedLookupColumnNativeStep_state_found]
          simpa [packedLookupColumnProcess] using
            induction remaining word digit true
      | false =>
          cases remaining with
          | nil =>
              rw [packedLookupColumnNativeStep_state_nil]
              simpa [packedLookupColumnProcess] using
                induction [] word digit false
          | cons cell remaining =>
              rw [packedLookupColumnNativeStep_state_cons]
              by_cases hit :
                  selected && decide (cell = target)
              · rw [if_pos hit]
                simpa [packedLookupColumnProcess, hit] using
                  induction remaining (word / 9) (word % 9) true
              · rw [if_neg hit]
                simpa [packedLookupColumnProcess, hit] using
                  induction remaining (word / 9) digit false

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

@[simp]
theorem packedLookupColumnScanState_not_selected_false
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) :
    packedLookupColumnScanState original target remaining
        word digit false false =
      packedLookupColumnState original [] target
        (word / 9 ^ remaining.length) digit false false := by
  induction remaining generalizing word with
  | nil =>
      simp [packedLookupColumnScanState,
        packedLookupColumnState]
  | cons cell remaining induction =>
      rw [packedLookupColumnScanState, if_neg (by simp)]
      rw [induction (word / 9)]
      apply congrArg (fun finalWord =>
        packedLookupColumnState original [] target
          finalWord digit false false)
      rw [Nat.div_div_eq_div_mul]
      simp only [List.length_cons, pow_succ]
      rw [Nat.mul_comm]

/-- Assemble the flat-loop input from
`[motifCode, targetCellCode, word, digit, found, selected]`. -/
def packedLookupColumnLoopInputCode : Code :=
  prepend (get 0) <|
    prepend (get 0) <|
      prepend (get 0) <|
        prepend (get 1) <|
          prepend (get 2) <|
            prepend (get 3) <|
              prepend (get 4) (get 5)

@[simp]
theorem packedLookupColumnLoopInputCode_eval
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    packedLookupColumnLoopInputCode.eval
        [Encodable.encode motif, Encodable.encode target,
          word, digit, found.toNat, selected.toNat] =
      pure
        (Encodable.encode motif ::
          packedLookupColumnState motif motif target
            word digit found selected) := by
  simp [packedLookupColumnLoopInputCode,
    packedLookupColumnState]

/-- Retain the original motif and target together with the residual word,
recorded digit, and found tag after one column scan. -/
def packedLookupColumnProjectionCode : Code :=
  prepend (get 1) <|
    prepend (get 2) <|
      prepend (get 3) <|
        prepend (get 4) (get 5)

@[simp]
theorem packedLookupColumnProjectionCode_eval_values
    (values : List Nat) :
    packedLookupColumnProjectionCode.eval values =
      pure
        [values[1]?.getD 0, values[2]?.getD 0,
          values[3]?.getD 0, values[4]?.getD 0,
          values[5]?.getD 0] := by
  simp [packedLookupColumnProjectionCode]

@[simp]
theorem packedLookupColumnProjectionCode_eval
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    packedLookupColumnProjectionCode.eval
        (packedLookupColumnState original remaining target
          word digit found selected) =
      pure
        [Encodable.encode original, Encodable.encode target,
          word, digit, found.toNat] := by
  simp [packedLookupColumnProjectionCode,
    packedLookupColumnState]

@[simp]
theorem packedLookupColumnScanState_original_field
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    (packedLookupColumnScanState original target remaining
        word digit found selected)[1]?.getD 0 =
      Encodable.encode original := by
  induction remaining generalizing word digit found with
  | nil =>
      cases found <;>
        simp [packedLookupColumnScanState,
          packedLookupColumnState]
  | cons cell remaining induction =>
      cases found with
      | true =>
          simp [packedLookupColumnScanState,
            packedLookupColumnState]
      | false =>
          by_cases hit : selected && decide (cell = target)
          · simp [packedLookupColumnScanState,
              packedLookupColumnState, hit]
          · simpa [packedLookupColumnScanState, hit] using
              induction (word / 9) digit false

@[simp]
theorem packedLookupColumnScanState_target_field
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    (packedLookupColumnScanState original target remaining
        word digit found selected)[2]?.getD 0 =
      Encodable.encode target := by
  induction remaining generalizing word digit found with
  | nil =>
      cases found <;>
        simp [packedLookupColumnScanState,
          packedLookupColumnState]
  | cons cell remaining induction =>
      cases found with
      | true =>
          simp [packedLookupColumnScanState,
            packedLookupColumnState]
      | false =>
          by_cases hit : selected && decide (cell = target)
          · simp [packedLookupColumnScanState,
              packedLookupColumnState, hit]
          · simpa [packedLookupColumnScanState, hit] using
              induction (word / 9) digit false

/-- Three live fields retained after one complete column scan. -/
def packedLookupColumnOutcome
    (target : Cell) (selected : Bool) :
    List Cell → Nat → Nat → Bool → Nat × Nat × Bool
  | _, word, digit, true => (word, digit, true)
  | [], word, digit, false => (word, digit, false)
  | cell :: remaining, word, digit, false =>
      if selected && decide (cell = target) then
        (word / 9, word % 9, true)
      else
        packedLookupColumnOutcome target selected remaining
          (word / 9) digit false

@[simp]
theorem packedLookupColumnOutcome_found
    (target : Cell) (selected : Bool)
    (remaining : List Cell) (word digit : Nat) :
    packedLookupColumnOutcome target selected remaining
        word digit true =
      (word, digit, true) := by
  cases remaining <;> rfl

@[simp]
theorem packedLookupColumnOutcome_not_selected
    (target : Cell) (remaining : List Cell)
    (word digit : Nat) :
    packedLookupColumnOutcome target false remaining
        word digit false =
      (word / 9 ^ remaining.length, digit, false) := by
  induction remaining generalizing word with
  | nil =>
      simp [packedLookupColumnOutcome]
  | cons cell remaining induction =>
      rw [packedLookupColumnOutcome, if_neg (by simp)]
      rw [induction (word / 9)]
      apply congrArg (fun finalWord =>
        (finalWord, digit, false))
      rw [Nat.div_div_eq_div_mul]
      simp only [List.length_cons, pow_succ]
      rw [Nat.mul_comm]

theorem packedLookupColumnOutcome_of_not_mem
    (target : Cell) (selected : Bool)
    (remaining : List Cell) (word digit : Nat)
    (absent : target ∉ remaining) :
    packedLookupColumnOutcome target selected remaining
        word digit false =
      (word / 9 ^ remaining.length, digit, false) := by
  induction remaining generalizing word with
  | nil =>
      simp [packedLookupColumnOutcome]
  | cons cell remaining induction =>
      have unequal : cell ≠ target := by
        intro equal
        exact absent (by simp [equal])
      have tailAbsent : target ∉ remaining := by
        intro member
        exact absent (by simp [member])
      rw [packedLookupColumnOutcome, if_neg (by simp [unequal])]
      rw [induction (word / 9) tailAbsent]
      apply congrArg (fun finalWord =>
        (finalWord, digit, false))
      rw [Nat.div_div_eq_div_mul]
      simp only [List.length_cons, pow_succ]
      rw [Nat.mul_comm]

theorem packedLookupColumnOutcome_selected_of_mem
    (target : Cell) (remaining : List Cell)
    (word digit : Nat) (member : target ∈ remaining) :
    packedLookupColumnOutcome target true remaining
        word digit false =
      (word /
          9 ^ (@List.idxOf Cell instBEqOfDecidableEq
            target remaining + 1),
        LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt
          word
          (@List.idxOf Cell instBEqOfDecidableEq
            target remaining),
        true) := by
  induction remaining generalizing word with
  | nil =>
      simp at member
  | cons cell remaining induction =>
      by_cases equal : cell = target
      · subst target
        simp [packedLookupColumnOutcome,
          LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt]
      · have targetNe : target ≠ cell := Ne.symm equal
        have idxCons :
            @List.idxOf Cell instBEqOfDecidableEq
                target (cell :: remaining) =
              Nat.succ
                (@List.idxOf Cell instBEqOfDecidableEq
                  target remaining) :=
          by
            letI : BEq Cell := instBEqOfDecidableEq
            exact List.idxOf_cons_ne remaining equal
        have tailMember : target ∈ remaining := by
          simpa [targetNe] using member
        rw [packedLookupColumnOutcome, if_neg (by simp [equal])]
        rw [induction (word / 9) tailMember]
        rw [idxCons]
        apply congrArg₂ (fun finalWord finalDigit =>
          (finalWord, finalDigit, true))
        · rw [Nat.div_div_eq_div_mul]
          simp [pow_succ, Nat.mul_comm]
        · rw [assignmentDigitAt_div_nine]

theorem packedLookupColumnOutcome_word_le
    (target : Cell) (selected : Bool)
    (remaining : List Cell) (word digit : Nat)
    (found : Bool) :
    (packedLookupColumnOutcome target selected remaining
      word digit found).1 ≤ word := by
  induction remaining generalizing word digit found with
  | nil =>
      cases found <;>
        simp [packedLookupColumnOutcome]
  | cons cell remaining induction =>
      cases found with
      | true =>
          simp [packedLookupColumnOutcome]
      | false =>
          by_cases hit : selected && decide (cell = target)
          · simp [packedLookupColumnOutcome, hit,
              Nat.div_le_self]
          · have tail :=
              induction (word / 9) digit false
            rw [packedLookupColumnOutcome, if_neg hit]
            exact tail.trans (Nat.div_le_self word 9)

theorem packedLookupColumnOutcome_digit_le
    (target : Cell) (selected : Bool)
    (remaining : List Cell) (word digit : Nat)
    (found : Bool) :
    (packedLookupColumnOutcome target selected remaining
      word digit found).2.1 ≤ digit + 8 := by
  induction remaining generalizing word digit found with
  | nil =>
      cases found <;>
        simp [packedLookupColumnOutcome]
  | cons cell remaining induction =>
      cases found with
      | true =>
          simp [packedLookupColumnOutcome]
      | false =>
          by_cases hit : selected && decide (cell = target)
          · have remainder : word % 9 < 9 :=
              Nat.mod_lt word (by omega)
            simp [packedLookupColumnOutcome, hit]
            omega
          · simpa [packedLookupColumnOutcome, hit] using
              induction (word / 9) digit false

theorem packedLookupColumnScanState_outcome_fields
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    let state :=
      packedLookupColumnScanState original target remaining
        word digit found selected
    let outcome :=
      packedLookupColumnOutcome target selected remaining
        word digit found
    [state[3]?.getD 0, state[4]?.getD 0, state[5]?.getD 0] =
      [outcome.1, outcome.2.1, outcome.2.2.toNat] := by
  induction remaining generalizing word digit found with
  | nil =>
      cases found <;>
        simp [packedLookupColumnScanState,
          packedLookupColumnState,
          packedLookupColumnOutcome]
  | cons cell remaining induction =>
      cases found with
      | true =>
          simp [packedLookupColumnScanState,
            packedLookupColumnState,
            packedLookupColumnOutcome]
      | false =>
          by_cases hit : selected && decide (cell = target)
          · simp [packedLookupColumnScanState,
              packedLookupColumnState,
              packedLookupColumnOutcome, hit]
          · simpa [packedLookupColumnScanState,
              packedLookupColumnOutcome, hit] using
              induction (word / 9) digit false

/-- Closed output of one complete packed column lookup. -/
def packedLookupColumnResult
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) : List Nat :=
  let final :=
    packedLookupColumnScanState motif target motif
      word digit found selected
  [Encodable.encode motif, Encodable.encode target,
    final[3]?.getD 0, final[4]?.getD 0, final[5]?.getD 0]

@[simp]
theorem packedLookupColumnResult_eq_outcome
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    packedLookupColumnResult motif target
        word digit found selected =
      let outcome :=
        packedLookupColumnOutcome target selected motif
          word digit found
      [Encodable.encode motif, Encodable.encode target,
        outcome.1, outcome.2.1, outcome.2.2.toNat] := by
  unfold packedLookupColumnResult
  have fields :=
    packedLookupColumnScanState_outcome_fields
      motif motif target word digit found selected
  simp only at fields
  simp [fields]

@[simp]
theorem packedLookupColumnResult_found
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) :
    packedLookupColumnResult motif target
        word digit true selected =
      [Encodable.encode motif, Encodable.encode target,
        word, digit, 1] := by
  simp [packedLookupColumnResult,
    packedLookupColumnScanState,
    packedLookupColumnState]

@[simp]
theorem packedLookupColumnResult_not_selected
    (motif : List Cell) (target : Cell)
    (word digit : Nat) :
    packedLookupColumnResult motif target
        word digit false false =
      [Encodable.encode motif, Encodable.encode target,
        word / 9 ^ motif.length, digit, 0] := by
  simp [packedLookupColumnResult,
    packedLookupColumnScanState_not_selected_false,
    packedLookupColumnState]

theorem packedLookupColumnResult_digit_selected_of_mem
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (member : target ∈ motif) :
    (packedLookupColumnResult motif target
        word digit false true)[3]?.getD 0 =
      LeanTrominoes.PeriodicStrip.RawWindowState.assignmentDigitAt
        word
        (@List.idxOf Cell instBEqOfDecidableEq target motif) := by
  simp only [packedLookupColumnResult, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  exact packedLookupColumnScanState_digit_of_mem
    motif motif target word digit member

theorem packedLookupColumnResult_found_selected_of_mem
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (member : target ∈ motif) :
    (packedLookupColumnResult motif target
        word digit false true)[4]?.getD 0 = 1 := by
  simp only [packedLookupColumnResult, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  exact packedLookupColumnScanState_found_of_mem
    motif motif target word digit member

/-- Complete explicit program for one motif-column lookup. -/
def packedLookupColumnCode : Code :=
  packedLookupColumnProjectionCode.comp <|
    (flatIterate packedLookupColumnStepCode).comp
      packedLookupColumnLoopInputCode

@[simp]
theorem packedLookupColumnCode_eval
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    packedLookupColumnCode.eval
        [Encodable.encode motif, Encodable.encode target,
          word, digit, found.toNat, selected.toNat] =
      pure
        (packedLookupColumnResult motif target
          word digit found selected) := by
  let input :=
    [Encodable.encode motif, Encodable.encode target,
      word, digit, found.toNat, selected.toNat]
  let process :=
    packedLookupColumnProcess motif target
      (Encodable.encode motif) motif
      word digit found selected
  have loopRun :
      ((flatIterate packedLookupColumnStepCode).comp
          packedLookupColumnLoopInputCode).eval input =
        pure process := by
    calc
      _ = (flatIterate packedLookupColumnStepCode).eval
          (Encodable.encode motif ::
            packedLookupColumnState motif motif target
              word digit found selected) :=
        comp_eval_pure _ _ _ _
          (packedLookupColumnLoopInputCode_eval
            motif target word digit found selected)
      _ = pure process := by
        exact packedLookupColumnFlatIterateCode_eval
          motif motif target (Encodable.encode motif)
          word digit found selected
  calc
    _ = packedLookupColumnProjectionCode.eval process :=
      comp_eval_pure _ _ _ _ loopRun
    _ = pure
        (packedLookupColumnResult motif target
          word digit found selected) := by
      simp [process, packedLookupColumnProcess_encode,
        packedLookupColumnResult]

end Turing.ToPartrec.Code

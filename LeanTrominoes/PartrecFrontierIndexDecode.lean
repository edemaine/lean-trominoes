import LeanTrominoes.PartrecDivision
import LeanTrominoes.StripFrontierIndex

/-!
# Explicit streaming decoder for frontier indices

The indexed strip search stores each frontier as one natural number.  With
the period in field zero, division exposes the base-nine assignment word and
the horizontal phase.  A second fixed divisor, nine, then peels one
assignment digit at a time.  These fixed-width views let the eventual edge
program traverse the input motif without materializing an assignment list.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState

/-- Assemble `[stateIndex, period]` when the period is field zero. -/
def frontierIndexArgumentsAtCode (indexField : Nat) : Code :=
  prepend (get indexField) (get 0)

@[simp]
theorem frontierIndexArgumentsAtCode_eval
    (indexField : Nat) (values : List Nat) :
    (frontierIndexArgumentsAtCode indexField).eval values =
      pure
        [values[indexField]?.getD 0,
          values[0]?.getD 0] := by
  simp [frontierIndexArgumentsAtCode]

/-- Decode one selected state index to `[assignmentWord, phase]`. -/
def frontierIndexViewAtCode (indexField : Nat) : Code :=
  divisionCode.comp (frontierIndexArgumentsAtCode indexField)

@[simp]
theorem frontierIndexViewAtCode_eval
    (indexField : Nat) (values : List Nat) :
    (frontierIndexViewAtCode indexField).eval values =
      pure
        [values[indexField]?.getD 0 /
            values[0]?.getD 0,
          values[indexField]?.getD 0 %
            values[0]?.getD 0] := by
  simp [frontierIndexViewAtCode]

/-- Select the assignment word or phase from one decoded index. -/
def frontierIndexFieldAtCode
    (indexField outputField : Nat) : Code :=
  (get outputField).comp
    (frontierIndexViewAtCode indexField)

@[simp]
theorem frontierIndexFieldAtCode_eval
    (indexField outputField : Nat)
    (values : List Nat) :
    (frontierIndexFieldAtCode
      indexField outputField).eval values =
      pure
        [[values[indexField]?.getD 0 /
              values[0]?.getD 0,
            values[indexField]?.getD 0 %
              values[0]?.getD 0][outputField]?.getD 0] := by
  simp [frontierIndexFieldAtCode]

/-- Decode `[period, firstIndex, lastIndex]` to
`[firstWord, firstPhase, lastWord, lastPhase]`. -/
def frontierPairViewCode : Code :=
  prepend (frontierIndexFieldAtCode 1 0) <|
    prepend (frontierIndexFieldAtCode 1 1) <|
      prepend (frontierIndexFieldAtCode 2 0)
        (frontierIndexFieldAtCode 2 1)

@[simp]
theorem frontierPairViewCode_eval
    (period first last : Nat) :
    frontierPairViewCode.eval [period, first, last] =
      pure
        [first / period, first % period,
          last / period, last % period] := by
  simp [frontierPairViewCode]

/-- Assemble `[assignmentWord, 9]` for one low-digit step. -/
def assignmentWordStepArgumentsAtCode
    (wordField : Nat) : Code :=
  prepend (get wordField) (numeral 9)

@[simp]
theorem assignmentWordStepArgumentsAtCode_eval
    (wordField : Nat) (values : List Nat) :
    (assignmentWordStepArgumentsAtCode wordField).eval values =
      pure [values[wordField]?.getD 0, 9] := by
  simp [assignmentWordStepArgumentsAtCode]

/-- Peel one selected base-nine word to `[tailWord, lowDigit]`. -/
def assignmentWordStepAtCode (wordField : Nat) : Code :=
  divisionCode.comp
    (assignmentWordStepArgumentsAtCode wordField)

@[simp]
theorem assignmentWordStepAtCode_eval
    (wordField : Nat) (values : List Nat) :
    (assignmentWordStepAtCode wordField).eval values =
      pure
        [values[wordField]?.getD 0 / 9,
          values[wordField]?.getD 0 % 9] := by
  simp [assignmentWordStepAtCode]

/-- Select the tail word or low digit from one word step. -/
def assignmentWordStepFieldAtCode
    (wordField outputField : Nat) : Code :=
  (get outputField).comp
    (assignmentWordStepAtCode wordField)

@[simp]
theorem assignmentWordStepFieldAtCode_eval
    (wordField outputField : Nat)
    (values : List Nat) :
    (assignmentWordStepFieldAtCode
      wordField outputField).eval values =
      pure
        [[values[wordField]?.getD 0 / 9,
            values[wordField]?.getD 0 % 9][outputField]?.getD 0] := by
  simp [assignmentWordStepFieldAtCode]

/-- Peel two words in parallel.  Input is `[firstWord, lastWord]`; output is
`[firstTail, firstDigit, lastTail, lastDigit]`. -/
def assignmentWordPairStepCode : Code :=
  prepend (assignmentWordStepFieldAtCode 0 0) <|
    prepend (assignmentWordStepFieldAtCode 0 1) <|
      prepend (assignmentWordStepFieldAtCode 1 0)
        (assignmentWordStepFieldAtCode 1 1)

@[simp]
theorem assignmentWordPairStepCode_eval
    (firstWord lastWord : Nat) :
    assignmentWordPairStepCode.eval [firstWord, lastWord] =
      pure
        [firstWord / 9, firstWord % 9,
          lastWord / 9, lastWord % 9] := by
  simp [assignmentWordPairStepCode]

/-- One streaming step exposes exactly the head symbol and residual word used
by `decodeAssignmentStream`. -/
theorem decodeAssignmentStream_succ
    (length word : Nat) :
    decodeAssignmentStream (length + 1) word =
      assignmentOfDigit (word % 9) ::
        decodeAssignmentStream length (word / 9) := by
  rfl

end Turing.ToPartrec.Code

import LeanTrominoes.PartrecPackedAssignmentLookup
import LeanTrominoes.PartrecEncodedListDecodeSpace
import LeanTrominoes.PartrecFrontierIndexDecodeSpace
import LeanTrominoes.PartrecNatEqualitySpace

/-!
# Evaluator-space certificate for packed assignment lookup steps

This module fits every component of the fixed-width packed lookup payload,
then fits the complete typed step and its flat-countdown body.  The subsequent
uniform-loop certificate can therefore reason only about bounds on reachable
motif suffixes and residual base-nine words.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedLookupColumnViewCost
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) : Nat :=
  encodedListViewCost remaining +
    getCost 0
      (Code.packedLookupColumnState original remaining target
        word digit found selected)

theorem packedLookupColumnView
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnViewCode
      (Code.packedLookupColumnState original remaining target
        word digit found selected)
      (match remaining with
      | [] => [0, 0, 0]
      | cell :: tail =>
          [1, Encodable.encode cell, Encodable.encode tail])
      (packedLookupColumnViewCost original remaining target
        word digit found selected) := by
  cases remaining with
  | nil =>
      simpa [Code.packedLookupColumnViewCode,
        packedLookupColumnViewCost] using
        comp (encodedListView ([] : List Cell))
          (get 0
            (Code.packedLookupColumnState original [] target
              word digit found selected))
  | cons cell remaining =>
      simpa [Code.packedLookupColumnViewCode,
        packedLookupColumnViewCost] using
        comp (encodedListView (cell :: remaining))
          (get 0
            (Code.packedLookupColumnState original
              (cell :: remaining) target
              word digit found selected))

def packedLookupColumnHeadCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  getCost 1
      [1, Encodable.encode cell, Encodable.encode remaining] +
    packedLookupColumnViewCost original (cell :: remaining)
      target word digit found selected

theorem packedLookupColumnHead
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnHeadCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      [Encodable.encode cell]
      (packedLookupColumnHeadCost original target cell remaining
        word digit found selected) := by
  simpa [Code.packedLookupColumnHeadCode,
    packedLookupColumnHeadCost] using
    comp
      (get 1
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (packedLookupColumnView original (cell :: remaining)
        target word digit found selected)

def packedLookupColumnTailCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  getCost 2
      [1, Encodable.encode cell, Encodable.encode remaining] +
    packedLookupColumnViewCost original (cell :: remaining)
      target word digit found selected

theorem packedLookupColumnTail
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnTailCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      [Encodable.encode remaining]
      (packedLookupColumnTailCost original target cell remaining
        word digit found selected) := by
  simpa [Code.packedLookupColumnTailCode,
    packedLookupColumnTailCost] using
    comp
      (get 2
        [1, Encodable.encode cell,
          Encodable.encode remaining])
      (packedLookupColumnView original (cell :: remaining)
        target word digit found selected)

def packedLookupColumnEqualityArgumentsCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit found selected
  prependCost state [Encodable.encode cell]
    [Encodable.encode target]
    (packedLookupColumnHeadCost original target cell remaining
      word digit found selected)
    (getCost 2 state)

theorem packedLookupColumnEqualityArguments
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnEqualityArgumentsCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      [Encodable.encode cell, Encodable.encode target]
      (packedLookupColumnEqualityArgumentsCost original target cell
        remaining word digit found selected) := by
  simpa [Code.packedLookupColumnEqualityArgumentsCode,
    packedLookupColumnEqualityArgumentsCost, prependCost,
    Code.packedLookupColumnState] using
    prepend
      (packedLookupColumnHead original target cell remaining
        word digit found selected)
      (get 2
        (Code.packedLookupColumnState original (cell :: remaining)
          target word digit found selected))

def packedLookupColumnEqualCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  natEqCost (Encodable.encode cell) (Encodable.encode target) +
    packedLookupColumnEqualityArgumentsCost original target cell
      remaining word digit found selected

theorem packedLookupColumnEqual
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits
      (Code.natEqCode.comp
        Code.packedLookupColumnEqualityArgumentsCode)
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      [if cell = target then 1 else 0]
      (packedLookupColumnEqualCost original target cell remaining
        word digit found selected) := by
  have equality :=
    comp
      (natEq (Encodable.encode cell) (Encodable.encode target))
      (packedLookupColumnEqualityArguments original target cell
        remaining word digit found selected)
  by_cases equal : cell = target
  · subst target
    simpa [packedLookupColumnEqualCost] using equality
  · have encodedNe :
        Encodable.encode cell ≠ Encodable.encode target := by
      intro encodedEqual
      exact equal (Encodable.encode_injective encodedEqual)
    simpa [packedLookupColumnEqualCost, equal, encodedNe] using
      equality

def packedLookupColumnMatchCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit found selected
  let equalTag := if cell = target then 1 else 0
  boolAndCost state selected.toNat equalTag
    (getCost 6 state)
    (packedLookupColumnEqualCost original target cell remaining
      word digit found selected)

theorem packedLookupColumnMatch
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnMatchCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      [(selected && decide (cell = target)).toNat]
      (packedLookupColumnMatchCost original target cell remaining
        word digit found selected) := by
  have combined :=
    boolAnd
      (get 6
        (Code.packedLookupColumnState original (cell :: remaining)
          target word digit found selected))
      (packedLookupColumnEqual original target cell remaining
        word digit found selected)
  cases selected <;>
    by_cases equal : cell = target <;>
    simp [Code.packedLookupColumnMatchCode,
      packedLookupColumnMatchCost, equal] at combined ⊢
  all_goals exact combined

def packedLookupColumnContinueCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit found selected
  let rest6 :=
    prependCost state [found.toNat] [selected.toNat]
      (getCost 5 state) (getCost 6 state)
  let rest5 :=
    prependCost state [digit] [found.toNat, selected.toNat]
      (getCost 4 state) rest6
  let rest4 :=
    prependCost state [word / 9]
      [digit, found.toNat, selected.toNat]
      (assignmentWordStepFieldAtCost 3 0 state) rest5
  let rest3 :=
    prependCost state [Encodable.encode target]
      [word / 9, digit, found.toNat, selected.toNat]
      (getCost 2 state) rest4
  let rest2 :=
    prependCost state [Encodable.encode original]
      [Encodable.encode target, word / 9, digit,
        found.toNat, selected.toNat]
      (getCost 1 state) rest3
  prependCost state [Encodable.encode remaining]
    [Encodable.encode original, Encodable.encode target,
      word / 9, digit, found.toNat, selected.toNat]
    (packedLookupColumnTailCost original target cell remaining
      word digit found selected)
    rest2

theorem packedLookupColumnContinue
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnContinueCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      (Code.packedLookupColumnState original remaining target
        (word / 9) digit found selected)
      (packedLookupColumnContinueCost original target cell remaining
        word digit found selected) := by
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit found selected
  have rest6 :=
    prepend (get 5 state) (get 6 state)
  have rest5 :=
    prepend (get 4 state) rest6
  have rest4 :=
    prepend
      (assignmentWordStepFieldAt 3 0 state) rest5
  have rest3 :=
    prepend (get 2 state) rest4
  have rest2 :=
    prepend (get 1 state) rest3
  have result :=
    prepend
      (packedLookupColumnTail original target cell remaining
        word digit found selected)
      rest2
  simpa [Code.packedLookupColumnContinueCode,
    packedLookupColumnContinueCost, prependCost,
    Code.packedLookupColumnState, state] using result

def packedLookupColumnFoundCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit found selected
  let rest6 :=
    prependCost state [1] [selected.toNat]
      (oneCost state) (getCost 6 state)
  let rest5 :=
    prependCost state [word % 9] [1, selected.toNat]
      (assignmentWordStepFieldAtCost 3 1 state) rest6
  let rest4 :=
    prependCost state [word / 9]
      [word % 9, 1, selected.toNat]
      (assignmentWordStepFieldAtCost 3 0 state) rest5
  let rest3 :=
    prependCost state [Encodable.encode target]
      [word / 9, word % 9, 1, selected.toNat]
      (getCost 2 state) rest4
  let rest2 :=
    prependCost state [Encodable.encode original]
      [Encodable.encode target, word / 9, word % 9,
        1, selected.toNat]
      (getCost 1 state) rest3
  prependCost state [Encodable.encode remaining]
    [Encodable.encode original, Encodable.encode target,
      word / 9, word % 9, 1, selected.toNat]
    (packedLookupColumnTailCost original target cell remaining
      word digit found selected)
    rest2

theorem packedLookupColumnFound
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnFoundCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit found selected)
      (Code.packedLookupColumnState original remaining target
        (word / 9) (word % 9) true selected)
      (packedLookupColumnFoundCost original target cell remaining
        word digit found selected) := by
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit found selected
  have rest6 :=
    prepend (one state) (get 6 state)
  have rest5 :=
    prepend
      (assignmentWordStepFieldAt 3 1 state) rest6
  have rest4 :=
    prepend
      (assignmentWordStepFieldAt 3 0 state) rest5
  have rest3 :=
    prepend (get 2 state) rest4
  have rest2 :=
    prepend (get 1 state) rest3
  have result :=
    prepend
      (packedLookupColumnTail original target cell remaining
        word digit found selected)
      rest2
  simpa [Code.packedLookupColumnFoundCode,
    packedLookupColumnFoundCost, prependCost,
    Code.packedLookupColumnState, state] using result

def packedLookupColumnConsStepCost
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original (cell :: remaining)
      target word digit false selected
  let hit := selected && decide (cell = target)
  if hit then
    branchZeroSuccCost state
      (Code.packedLookupColumnState original remaining target
        (word / 9) (word % 9) true selected)
      hit.toNat
      (packedLookupColumnMatchCost original target cell remaining
        word digit false selected)
      (packedLookupColumnFoundCost original target cell remaining
        word digit false selected)
  else
    branchZeroZeroCost state
      (Code.packedLookupColumnState original remaining target
        (word / 9) digit false selected)
      hit.toNat
      (packedLookupColumnMatchCost original target cell remaining
        word digit false selected)
      (packedLookupColumnContinueCost original target cell remaining
        word digit false selected)

theorem packedLookupColumnConsStep
    (original : List Cell) (target cell : Cell)
    (remaining : List Cell) (word digit : Nat)
    (selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnConsStepCode
      (Code.packedLookupColumnState original (cell :: remaining)
        target word digit false selected)
      (Code.packedLookupColumnNativeStep
        (Code.packedLookupColumnState original (cell :: remaining)
          target word digit false selected))
      (packedLookupColumnConsStepCost original target cell remaining
        word digit selected) := by
  by_cases hit : selected && decide (cell = target)
  · simpa [Code.packedLookupColumnConsStepCode,
      packedLookupColumnConsStepCost,
      Code.packedLookupColumnNativeStep_state_cons, hit] using
      branchZero_succ (by simp [hit])
        (packedLookupColumnMatch original target cell remaining
          word digit false selected)
        (packedLookupColumnFound original target cell remaining
          word digit false selected)
  · simpa [Code.packedLookupColumnConsStepCode,
      packedLookupColumnConsStepCost,
      Code.packedLookupColumnNativeStep_state_cons, hit] using
      branchZero_zero (by simp [hit])
        (packedLookupColumnMatch original target cell remaining
          word digit false selected)
        (packedLookupColumnContinue original target cell remaining
          word digit false selected)

def packedLookupColumnInnerStepCost
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original remaining target
      word digit false selected
  match remaining with
  | [] =>
      branchZeroZeroCost state state 0
        (getCost 0 state) (idCost state)
  | cell :: tail =>
      branchZeroSuccCost state
        (Code.packedLookupColumnNativeStep state)
        (Encodable.encode (cell :: tail))
        (getCost 0 state)
        (packedLookupColumnConsStepCost original target cell tail
          word digit selected)

theorem packedLookupColumnInnerStep
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (selected : Bool) :
    EvaluatorCodeFits
      (Code.branchZero (Code.get 0) Code.id
        Code.packedLookupColumnConsStepCode)
      (Code.packedLookupColumnState original remaining target
        word digit false selected)
      (Code.packedLookupColumnNativeStep
        (Code.packedLookupColumnState original remaining target
          word digit false selected))
      (packedLookupColumnInnerStepCost original remaining target
        word digit selected) := by
  cases remaining with
  | nil =>
      simpa [packedLookupColumnInnerStepCost] using
        branchZero_zero rfl
          (get 0
            (Code.packedLookupColumnState original [] target
              word digit false selected))
          (id
            (Code.packedLookupColumnState original [] target
              word digit false selected))
  | cons cell remaining =>
      have positive :
          0 < Encodable.encode (cell :: remaining) := by
        simp
      simpa [packedLookupColumnInnerStepCost] using
        branchZero_succ positive
          (get 0
            (Code.packedLookupColumnState original
              (cell :: remaining) target
              word digit false selected))
          (packedLookupColumnConsStep original target cell remaining
            word digit selected)

def packedLookupColumnStepCost
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) : Nat :=
  let state :=
    Code.packedLookupColumnState original remaining target
      word digit found selected
  if found then
    branchZeroSuccCost state state found.toNat
      (getCost 5 state) (idCost state)
  else
    branchZeroZeroCost state
      (Code.packedLookupColumnNativeStep state) found.toNat
      (getCost 5 state)
      (packedLookupColumnInnerStepCost original remaining target
        word digit selected)

theorem packedLookupColumnStep
    (original remaining : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnStepCode
      (Code.packedLookupColumnState original remaining target
        word digit found selected)
      (Code.packedLookupColumnNativeStep
        (Code.packedLookupColumnState original remaining target
          word digit found selected))
      (packedLookupColumnStepCost original remaining target
        word digit found selected) := by
  cases found with
  | true =>
      simpa [Code.packedLookupColumnStepCode,
        packedLookupColumnStepCost] using
        branchZero_succ (testValue := 1) (by omega)
          (get 5
            (Code.packedLookupColumnState original remaining target
              word digit true selected))
          (id
            (Code.packedLookupColumnState original remaining target
              word digit true selected))
  | false =>
      simpa [Code.packedLookupColumnStepCode,
        packedLookupColumnStepCost] using
        branchZero_zero rfl
          (get 5
            (Code.packedLookupColumnState original remaining target
              word digit false selected))
          (packedLookupColumnInnerStep original remaining target
            word digit selected)

def packedLookupColumnBodyCost
    (steps : Nat) (original remaining : List Cell)
    (target : Cell) (word digit : Nat)
    (found selected : Bool) : Nat :=
  flatCountdownBodyCost Code.packedLookupColumnNativeStep
    (fun _ =>
      packedLookupColumnStepCost original remaining target
        word digit found selected)
    steps
    (Code.packedLookupColumnState original remaining target
      word digit found selected)

theorem packedLookupColumnBody
    (steps : Nat) (original remaining : List Cell)
    (target : Cell) (word digit : Nat)
    (found selected : Bool) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.packedLookupColumnStepCode)
      (steps ::
        Code.packedLookupColumnState original remaining target
          word digit found selected)
      (flatCountdownOutput Code.packedLookupColumnNativeStep
        steps
        (Code.packedLookupColumnState original remaining target
          word digit found selected))
      (packedLookupColumnBodyCost steps original remaining target
        word digit found selected) := by
  cases steps with
  | zero =>
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, packedLookupColumnBodyCost,
        flatCountdownBodyCost, zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one
              (.cons Code.head
                (Code.packedLookupColumnStepCode.comp Code.tail)))
          (values :=
            0 ::
              Code.packedLookupColumnState original remaining target
                word digit found selected)
          (by rfl)
          (zero'_named
            (Code.packedLookupColumnState original remaining target
              word digit found selected))
  | succ steps =>
      let payload :=
        Code.packedLookupColumnState original remaining target
          word digit found selected
      let values := steps :: payload
      have transformed :=
        comp
          (packedLookupColumnStep original remaining target
            word digit found selected)
          (tail_named values)
      have payloadResult :=
        prepend (head values) transformed
      have branch :=
        prepend (one values) payloadResult
      simpa [Code.flatCountdownBody,
        flatCountdownOutput, packedLookupColumnBodyCost,
        flatCountdownBodyCost,
        flatCountdownSuccBranchCost,
        payload, values, prependCost,
        Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values := (steps + 1) :: payload)
          (predecessor := steps)
          (by rfl) branch

end EvaluatorCodeFits

end PartrecToTM2
end Turing

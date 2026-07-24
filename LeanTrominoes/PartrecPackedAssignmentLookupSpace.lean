import LeanTrominoes.PartrecPackedAssignmentLookup
import LeanTrominoes.PartrecEncodedListDecodeSpace
import LeanTrominoes.PartrecFrontierIndexDecodeSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecStripWellFormedSpace

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

set_option maxHeartbeats 1600000 in
theorem packedLookupColumnBodyCost_le_linear
    (steps : Nat) (original remaining : List Cell)
    (target : Cell) (word digit : Nat)
    (found selected : Bool) :
    packedLookupColumnBodyCost steps original remaining target
        word digit found selected ≤
      10000000000000000 *
        (encodedListSpace
          [16 * (steps + Encodable.encode original +
            Encodable.encode remaining + Encodable.encode target +
            word + digit) + 100] + 1) := by
  let originalCode := Encodable.encode original
  let remainingCode := Encodable.encode remaining
  let targetCode := Encodable.encode target
  let limit :=
    16 * (steps + originalCode + remainingCode +
      targetCode + word + digit) + 100
  have stepsBound : steps ≤ limit := by
    simp only [limit]
    omega
  have originalBound : originalCode ≤ limit := by
    simp only [limit]
    omega
  have remainingBound : remainingCode ≤ limit := by
    simp only [limit]
    omega
  have targetBound : targetCode ≤ limit := by
    simp only [limit]
    omega
  have wordBound : word ≤ limit := by
    simp only [limit]
    omega
  have digitBound : digit ≤ limit := by
    simp only [limit]
    omega
  have stepsBits := encodeNat_length_mono stepsBound
  have stepsPredBits :=
    encodeNat_length_mono ((Nat.pred_le steps).trans stepsBound)
  have stepsSuccBits :=
    encodeNat_length_mono
      (show steps + 1 ≤ limit by
        simp only [limit]
        omega)
  have originalBits := encodeNat_length_mono originalBound
  have remainingBits := encodeNat_length_mono remainingBound
  have targetBits := encodeNat_length_mono targetBound
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitBound
  have originalSuccBits :=
    encodeNat_length_mono
      (show originalCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have remainingSuccBits :=
    encodeNat_length_mono
      (show remainingCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have targetSuccBits :=
    encodeNat_length_mono
      (show targetCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show word + 1 ≤ limit by
        simp only [limit]
        omega)
  have digitSuccBits :=
    encodeNat_length_mono
      (show digit + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordTailBound : word / 9 ≤ limit :=
    (Nat.div_le_self word 9).trans wordBound
  have wordDigitBound : word % 9 ≤ limit :=
    (Nat.mod_le word 9).trans wordBound
  have wordTailBits := encodeNat_length_mono wordTailBound
  have wordDigitBits := encodeNat_length_mono wordDigitBound
  have wordTailSuccBits :=
    encodeNat_length_mono
      (show word / 9 + 1 ≤ limit by
        simp only [limit]
        have := Nat.div_le_self word 9
        omega)
  have wordDigitSuccBits :=
    encodeNat_length_mono
      (show word % 9 + 1 ≤ limit by
        simp only [limit]
        have := Nat.mod_le word 9
        omega)
  have viewBound := encodedListViewCost_le_linear remaining
  have viewLimit :
      encodedListSpace [2 * remainingCode + 4] ≤
        encodedListSpace [limit] := by
    have numeric : 2 * remainingCode + 4 ≤ limit := by
      simp only [limit]
      omega
    simpa only [encodedListSpace_cons,
      encodedListSpace_nil, Nat.add_le_add_iff_right] using
      encodeNat_length_mono numeric
  have divisionLimit :
      encodedListSpace [8 * (word + 9) + 16] ≤
        encodedListSpace [limit] := by
    have numeric : 8 * (word + 9) + 16 ≤ limit := by
      simp only [limit]
      omega
    simpa only [encodedListSpace_cons,
      encodedListSpace_nil, Nat.add_le_add_iff_right] using
      encodeNat_length_mono numeric
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have fourBits :
      (Computability.encodeNat 4).length = 3 := rfl
  have nineBits :
      (Computability.encodeNat 9).length = 4 := rfl
  have oneLimitBits :=
    encodeNat_length_mono
      (show 1 ≤ limit by
        simp only [limit]
        omega)
  have positiveLimitBits :
      1 ≤ (Computability.encodeNat limit).length := by
    simpa [oneBits] using oneLimitBits
  have foundBits :
      (Computability.encodeNat found.toNat).length ≤
        (Computability.encodeNat limit).length := by
    cases found
    · simp [zeroBits]
    · simpa [oneBits] using positiveLimitBits
  have selectedBits :
      (Computability.encodeNat selected.toNat).length ≤
        (Computability.encodeNat limit).length := by
    cases selected
    · simp [zeroBits]
    · simpa [oneBits] using positiveLimitBits
  have numeralNineBound := addConstCost_le 9 [0]
  cases remaining with
  | nil =>
      cases steps <;>
        cases found <;>
        simp [packedLookupColumnBodyCost,
          packedLookupColumnStepCost,
          packedLookupColumnInnerStepCost,
          flatCountdownBodyCost,
          flatCountdownSuccBranchCost,
          branchZeroZeroCost, branchZeroSuccCost,
          branchZeroTestCost, prependCost,
          getCost, dropCost, idCost, headCost,
          nilCost, oneCost, zeroCost, zeroPrimeCost,
          tailCost, succCost,
          Code.packedLookupColumnState,
          Code.packedLookupColumnNativeStep,
          encodedListSpace_cons, encodedListSpace_nil,
          originalCode, remainingCode, targetCode, limit,
          zeroBits, oneBits, twoBits, fourBits, nineBits] at * <;>
        omega
  | cons cell remaining =>
      let cellCode := Encodable.encode cell
      let tailCode := Encodable.encode remaining
      have cellRemaining :
          cellCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons, cellCode]
        exact (Nat.left_le_pair cellCode tailCode).trans
          (Nat.le_succ _)
      have tailRemaining :
          tailCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons, tailCode]
        exact (Nat.right_le_pair cellCode tailCode).trans
          (Nat.le_succ _)
      have cellLimit :
          cellCode ≤ limit :=
        cellRemaining.trans (by
          simpa [remainingCode] using remainingBound)
      have tailLimit :
          tailCode ≤ limit :=
        tailRemaining.trans (by
          simpa [remainingCode] using remainingBound)
      have cellBits := encodeNat_length_mono cellLimit
      have tailBits := encodeNat_length_mono tailLimit
      have constructorBits :=
        encodeNat_length_mono
          (show Nat.pair cellCode tailCode ≤ limit by
            exact (Nat.le_succ _).trans
              (by simpa [remainingCode] using remainingBound))
      have cellSuccBits :=
        encodeNat_length_mono
          (show cellCode + 1 ≤ limit by
            simp only [limit]
            omega)
      have tailSuccBits :=
        encodeNat_length_mono
          (show tailCode + 1 ≤ limit by
            simp only [limit]
            omega)
      have cellTargetCostBound :=
        natEqCost_le_linear cellCode targetCode
      have equalityLimit :
          encodedListSpace [2 * (cellCode + targetCode) + 4] ≤
            encodedListSpace [limit] := by
        have numeric :
            2 * (cellCode + targetCode) + 4 ≤ limit := by
          simp only [limit]
          omega
        simpa only [encodedListSpace_cons,
          encodedListSpace_nil, Nat.add_le_add_iff_right] using
          encodeNat_length_mono numeric
      cases steps with
      | zero =>
          simp [packedLookupColumnBodyCost,
            flatCountdownBodyCost, zeroPrimeCost,
            Code.packedLookupColumnState,
            encodedListSpace_cons, encodedListSpace_nil,
            originalCode, remainingCode, targetCode, limit,
            zeroBits, oneBits, twoBits, fourBits, nineBits] at *
          omega
      | succ steps =>
          cases found with
          | true =>
              simp [packedLookupColumnBodyCost,
                packedLookupColumnStepCost,
                flatCountdownBodyCost,
                flatCountdownSuccBranchCost,
                branchZeroSuccCost, branchZeroTestCost,
                prependCost, getCost, dropCost, idCost,
                headCost, nilCost, oneCost, zeroCost,
                zeroPrimeCost, tailCost, succCost,
                Code.packedLookupColumnState,
                Code.packedLookupColumnNativeStep,
                encodedListSpace_cons, encodedListSpace_nil,
                originalCode, remainingCode, targetCode, limit,
                zeroBits, oneBits, twoBits, fourBits, nineBits] at *
              omega
          | false =>
              cases selected <;>
                by_cases equal : cell = target <;>
                simp [packedLookupColumnBodyCost,
                  packedLookupColumnStepCost,
                  packedLookupColumnInnerStepCost,
                  packedLookupColumnConsStepCost,
                  packedLookupColumnMatchCost,
                  packedLookupColumnEqualCost,
                  packedLookupColumnEqualityArgumentsCost,
                  packedLookupColumnHeadCost,
                  packedLookupColumnTailCost,
                  packedLookupColumnViewCost,
                  packedLookupColumnContinueCost,
                  packedLookupColumnFoundCost,
                  assignmentWordStepFieldAtCost,
                  assignmentWordStepAtCost,
                  assignmentWordStepArgumentsAtCost,
                  divisionSpaceBound,
                  flatCountdownBodyCost,
                  flatCountdownSuccBranchCost,
                  branchZeroZeroCost, branchZeroSuccCost,
                  branchZeroTestCost, boolAndCost,
                  normalizeBoolCost, prependCost,
                  numeralCost,
                  getCost, dropCost, idCost, headCost,
                  nilCost, oneCost, zeroCost,
                  zeroPrimeCost, tailCost, succCost,
                  Code.packedLookupColumnState,
                  Code.packedLookupColumnNativeStep,
                  encodedListSpace_cons, encodedListSpace_nil,
                  originalCode, remainingCode, targetCode,
                  cellCode, tailCode, limit, equal,
                  zeroBits, oneBits, twoBits, fourBits,
                  nineBits] at * <;>
                omega

/-- One workspace allowance large enough for every reachable suffix state of
one complete motif-column lookup. -/
def packedLookupColumnSpaceBound
    (original : List Cell) (target : Cell)
    (word digit : Nat) : Nat :=
  10000000000000000 *
    (encodedListSpace
      [16 * (Encodable.encode original +
        Encodable.encode original + Encodable.encode original +
        Encodable.encode target + word + digit + 8) + 100] + 1)

/-- Typed states reachable while a packed lookup countdown is running. -/
def PackedLookupColumnReachable
    (original : List Cell) (target : Cell)
    (initialWord initialDigit : Nat) (selected : Bool)
    (steps : Nat) (values : List Nat) : Prop :=
  ∃ remaining leading word digit found,
    values =
      Code.packedLookupColumnState original remaining target
        word digit found selected ∧
    steps ≤ Encodable.encode original ∧
    original = leading ++ remaining ∧
    word ≤ initialWord ∧
    digit ≤ initialDigit + 8

theorem packedLookupColumnReachable_initial
    (original : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    PackedLookupColumnReachable original target word digit selected
      (Encodable.encode original)
      (Code.packedLookupColumnState original original target
        word digit found selected) := by
  exact ⟨original, [], word, digit, found,
    rfl, Nat.le_refl _, by simp, Nat.le_refl _, by omega⟩

theorem packedLookupColumnReachable_step
    (original : List Cell) (target : Cell)
    (initialWord initialDigit : Nat) (selected : Bool)
    (steps : Nat) (values : List Nat)
    (reachable :
      PackedLookupColumnReachable original target
        initialWord initialDigit selected (steps + 1) values) :
    PackedLookupColumnReachable original target
      initialWord initialDigit selected steps
      (Code.packedLookupColumnNativeStep values) := by
  obtain ⟨remaining, leading, word, digit, found, rfl,
    stepsBound, suffix, wordBound, digitBound⟩ := reachable
  cases found with
  | true =>
      exact ⟨remaining, leading, word, digit, true,
        Code.packedLookupColumnNativeStep_state_found
          original remaining target word digit selected,
        by omega, suffix, wordBound, digitBound⟩
  | false =>
      cases remaining with
      | nil =>
          exact ⟨[], leading, word, digit, false,
            Code.packedLookupColumnNativeStep_state_nil
              original target word digit selected,
            by omega, suffix, wordBound, digitBound⟩
      | cons cell remaining =>
          by_cases hit : selected && decide (cell = target)
          · refine
              ⟨remaining, leading ++ [cell],
                word / 9, word % 9, true, ?_,
                by omega, ?_, ?_, ?_⟩
            · simp [Code.packedLookupColumnNativeStep_state_cons,
                hit]
            · simpa [List.append_assoc] using suffix
            · exact (Nat.div_le_self word 9).trans wordBound
            · have lowDigit : word % 9 ≤ 8 := by
                have := Nat.mod_lt word (by omega : 0 < 9)
                omega
              omega
          · refine
              ⟨remaining, leading ++ [cell],
                word / 9, digit, false, ?_,
                by omega, ?_, ?_, digitBound⟩
            · simp [Code.packedLookupColumnNativeStep_state_cons,
                hit]
            · simpa [List.append_assoc] using suffix
            · exact (Nat.div_le_self word 9).trans wordBound

theorem packedLookupColumnBodyCost_le_spaceBound
    (original remaining leading : List Cell) (target : Cell)
    (initialWord initialDigit steps word digit : Nat)
    (found selected : Bool)
    (stepsBound : steps ≤ Encodable.encode original)
    (suffix : original = leading ++ remaining)
    (wordBound : word ≤ initialWord)
    (digitBound : digit ≤ initialDigit + 8) :
    packedLookupColumnBodyCost steps original remaining target
        word digit found selected ≤
      packedLookupColumnSpaceBound original target
        initialWord initialDigit := by
  let localLimit :=
    16 * (steps + Encodable.encode original +
      Encodable.encode remaining + Encodable.encode target +
      word + digit) + 100
  let globalLimit :=
    16 * (Encodable.encode original +
      Encodable.encode original + Encodable.encode original +
      Encodable.encode target + initialWord + initialDigit + 8) + 100
  have remainingBound :
      Encodable.encode remaining ≤ Encodable.encode original := by
    rw [suffix]
    exact encode_list_suffix_le leading remaining
  have numeric : localLimit ≤ globalLimit := by
    simp only [localLimit, globalLimit]
    omega
  have bits := encodeNat_length_mono numeric
  have body :=
    packedLookupColumnBodyCost_le_linear steps original remaining
      target word digit found selected
  have bodyLocal :
      packedLookupColumnBodyCost steps original remaining target
          word digit found selected ≤
        10000000000000000 *
          ((Computability.encodeNat localLimit).length + 1 + 1) := by
    simpa only [localLimit, encodedListSpace_cons,
      encodedListSpace_nil] using body
  simp only [packedLookupColumnSpaceBound,
    encodedListSpace_cons, encodedListSpace_nil]
  change
    packedLookupColumnBodyCost steps original remaining target
        word digit found selected ≤
      10000000000000000 *
        ((Computability.encodeNat globalLimit).length + 1 + 1)
  simp only [globalLimit] at bits ⊢
  omega

theorem packedLookupColumnReachable_iterate
    (original : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool)
    (steps taken : Nat)
    (total : steps + taken = Encodable.encode original) :
    PackedLookupColumnReachable original target word digit selected
      steps
      (((Code.packedLookupColumnNativeStep)^[taken])
        (Code.packedLookupColumnState original original target
          word digit found selected)) := by
  induction taken generalizing steps with
  | zero =>
      have stepsEq : steps = Encodable.encode original := by
        simpa using total
      subst steps
      simpa using
        packedLookupColumnReachable_initial
          original target word digit found selected
  | succ taken induction =>
      have previousTotal :
          (steps + 1) + taken = Encodable.encode original := by
        omega
      have previous := induction (steps + 1) previousTotal
      rw [Function.iterate_succ_apply']
      exact packedLookupColumnReachable_step
        original target word digit selected steps _ previous

/-- The complete packed lookup loop reuses one input-sized workspace bound
at every numeric-countdown iteration. -/
theorem packedLookupColumnFlatUniform
    (original : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    EvaluatorCodeFits
      (Code.flatIterate Code.packedLookupColumnStepCode)
      (Encodable.encode original ::
        Code.packedLookupColumnState original original target
          word digit found selected)
      (Code.packedLookupColumnProcess original target
        (Encodable.encode original) original
        word digit found selected)
      (packedLookupColumnSpaceBound original target word digit) where
  input_space := by
    have body :=
      packedLookupColumnBody (Encodable.encode original)
        original original target word digit found selected
    exact body.input_space.trans
      (packedLookupColumnBodyCost_le_spaceBound
        original original [] target word digit
        (Encodable.encode original) word digit found selected
        (Nat.le_refl _) (by simp) (Nat.le_refl _) (by omega))
  output_space := by
    have finalReachable :=
      packedLookupColumnReachable_iterate
        original target word digit found selected
        0 (Encodable.encode original) (by simp)
    obtain ⟨remaining, leading, finalWord, finalDigit, finalFound,
      resultEq, stepsBound, suffix, wordBound, digitBound⟩ :=
      finalReachable
    rw [Code.packedLookupColumnNativeStep_iterate] at resultEq
    rw [resultEq]
    have body :=
      packedLookupColumnBody 0 original remaining target
        finalWord finalDigit finalFound selected
    have boundedInput := body.input_space.trans
      (packedLookupColumnBodyCost_le_spaceBound
        original remaining leading target word digit
        0 finalWord finalDigit finalFound selected
        stepsBound suffix wordBound digitBound)
    have stateSpace :
        encodedListSpace
            (Code.packedLookupColumnState original remaining target
              finalWord finalDigit finalFound selected) ≤
          encodedListSpace
            (0 ::
              Code.packedLookupColumnState original remaining target
                finalWord finalDigit finalFound selected) := by
      simp [encodedListSpace_cons]
    exact stateSpace.trans boundedInput
  call continuation bound budget after := by
    apply
      EvaluatorCallFits.flatIterate_of_reachable_code_fits
        (step := Code.packedLookupColumnNativeStep)
        (bodyCost := fun _ _ =>
          packedLookupColumnSpaceBound original target word digit)
        (invariant :=
          PackedLookupColumnReachable original target
            word digit selected)
    · intro steps values reachable
      obtain ⟨remaining, leading, currentWord, currentDigit,
        currentFound, rfl, stepsBound, suffix,
        wordBound, digitBound⟩ := reachable
      exact
        (packedLookupColumnBody steps original remaining target
          currentWord currentDigit currentFound selected).mono
          (packedLookupColumnBodyCost_le_spaceBound
            original remaining leading target word digit
            steps currentWord currentDigit currentFound selected
            stepsBound suffix wordBound digitBound)
    · exact packedLookupColumnReachable_initial
        original target word digit found selected
    · exact packedLookupColumnReachable_step
        original target word digit selected
    · intro steps values reachable
      exact budget
    · rw [Code.packedLookupColumnNativeStep_iterate]
      exact after

def packedLookupColumnLoopInputCost
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) : Nat :=
  let values :=
    [Encodable.encode motif, Encodable.encode target,
      word, digit, found.toNat, selected.toNat]
  let rest7 :=
    prependCost values [found.toNat] [selected.toNat]
      (getCost 4 values) (getCost 5 values)
  let rest6 :=
    prependCost values [digit] [found.toNat, selected.toNat]
      (getCost 3 values) rest7
  let rest5 :=
    prependCost values [word]
      [digit, found.toNat, selected.toNat]
      (getCost 2 values) rest6
  let rest4 :=
    prependCost values [Encodable.encode target]
      [word, digit, found.toNat, selected.toNat]
      (getCost 1 values) rest5
  let rest3 :=
    prependCost values [Encodable.encode motif]
      [Encodable.encode target, word, digit,
        found.toNat, selected.toNat]
      (getCost 0 values) rest4
  let rest2 :=
    prependCost values [Encodable.encode motif]
      [Encodable.encode motif, Encodable.encode target,
        word, digit, found.toNat, selected.toNat]
      (getCost 0 values) rest3
  prependCost values [Encodable.encode motif]
    [Encodable.encode motif, Encodable.encode motif,
      Encodable.encode target, word, digit,
      found.toNat, selected.toNat]
    (getCost 0 values) rest2

theorem packedLookupColumnLoopInput
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnLoopInputCode
      [Encodable.encode motif, Encodable.encode target,
        word, digit, found.toNat, selected.toNat]
      (Encodable.encode motif ::
        Code.packedLookupColumnState motif motif target
          word digit found selected)
      (packedLookupColumnLoopInputCost motif target
        word digit found selected) := by
  let values :=
    [Encodable.encode motif, Encodable.encode target,
      word, digit, found.toNat, selected.toNat]
  have rest7 := prepend (get 4 values) (get 5 values)
  have rest6 := prepend (get 3 values) rest7
  have rest5 := prepend (get 2 values) rest6
  have rest4 := prepend (get 1 values) rest5
  have rest3 := prepend (get 0 values) rest4
  have rest2 := prepend (get 0 values) rest3
  have result := prepend (get 0 values) rest2
  simpa [Code.packedLookupColumnLoopInputCode,
    packedLookupColumnLoopInputCost, prependCost,
    Code.packedLookupColumnState, values] using result

def packedLookupColumnProjectionValuesCost
    (values : List Nat) : Nat :=
  let rest5 :=
    prependCost values [values[4]?.getD 0]
      [values[5]?.getD 0]
      (getCost 4 values) (getCost 5 values)
  let rest4 :=
    prependCost values [values[3]?.getD 0]
      [values[4]?.getD 0, values[5]?.getD 0]
      (getCost 3 values) rest5
  let rest3 :=
    prependCost values [values[2]?.getD 0]
      [values[3]?.getD 0, values[4]?.getD 0,
        values[5]?.getD 0]
      (getCost 2 values) rest4
  prependCost values [values[1]?.getD 0]
    [values[2]?.getD 0, values[3]?.getD 0,
      values[4]?.getD 0, values[5]?.getD 0]
    (getCost 1 values) rest3

theorem packedLookupColumnProjectionValues
    (values : List Nat) :
    EvaluatorCodeFits Code.packedLookupColumnProjectionCode
      values
      [values[1]?.getD 0, values[2]?.getD 0,
        values[3]?.getD 0, values[4]?.getD 0,
        values[5]?.getD 0]
      (packedLookupColumnProjectionValuesCost values) := by
  have rest5 := prepend (get 4 values) (get 5 values)
  have rest4 := prepend (get 3 values) rest5
  have rest3 := prepend (get 2 values) rest4
  have result := prepend (get 1 values) rest3
  simpa [Code.packedLookupColumnProjectionCode,
    packedLookupColumnProjectionValuesCost,
    prependCost] using result

def packedLookupColumnCodeCost
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) : Nat :=
  let process :=
    Code.packedLookupColumnProcess motif target
      (Encodable.encode motif) motif
      word digit found selected
  packedLookupColumnProjectionValuesCost process +
    (packedLookupColumnSpaceBound motif target word digit +
      packedLookupColumnLoopInputCost motif target
        word digit found selected)

theorem packedLookupColumn
    (motif : List Cell) (target : Cell)
    (word digit : Nat) (found selected : Bool) :
    EvaluatorCodeFits Code.packedLookupColumnCode
      [Encodable.encode motif, Encodable.encode target,
        word, digit, found.toNat, selected.toNat]
      (Code.packedLookupColumnResult motif target
        word digit found selected)
      (packedLookupColumnCodeCost motif target
        word digit found selected) := by
  let process :=
    Code.packedLookupColumnProcess motif target
      (Encodable.encode motif) motif
      word digit found selected
  have loop :=
    comp
      (packedLookupColumnFlatUniform motif target
        word digit found selected)
      (packedLookupColumnLoopInput motif target
        word digit found selected)
  have projected :=
    packedLookupColumnProjectionValues process
  have result := comp projected loop
  simpa [Code.packedLookupColumnCode,
    packedLookupColumnCodeCost, process,
    Code.packedLookupColumnResult,
    Code.packedLookupColumnProcess_encode] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing

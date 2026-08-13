import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecFlatPackedCenterBaseSpace
import LeanTrominoes.PartrecFlatPackedCenterLoop
import LeanTrominoes.PartrecFlatPackedNormalizationAtSpace

/-!
# Evaluator-space certificate for motif-wide flat center validity

The exact one-base center predicate is lifted through the explicit motif-length
countdown.  Each reachable scan state retains the original flat coordinate
stream, so one native polynomial envelope applies at every step.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedCenterBaseBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current : PackedWindowState) (cell : Cell) : Bool :=
  current.centerBaseInsideBool tromino periodicStrip cell &&
    current.centerBaseCoveredBool tromino periodicStrip cell

def flatPackedCenterBaseArgumentsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let coordinates := values.drop 9
  let restWord := prependCost values [current.assignmentWord] coordinates
    (getCost 5 values) (dropCost 9 values)
  let restY := prependCost values [Encodable.encode cell.2]
    (current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
      valid processed.length) restWord
  let restX := prependCost values [Encodable.encode cell.1]
    (Encodable.encode cell.2 :: current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
      valid processed.length) restY
  let restLength := prependCost values [periodicStrip.motif.length]
    (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates)
    (getCost 4 values) restX
  let restPhase := prependCost values [current.phase]
    (periodicStrip.motif.length :: Encodable.encode cell.1 ::
      Encodable.encode cell.2 :: current.assignmentWord :: coordinates)
    (getCost 6 values) restLength
  prependCost values [periodicStrip.period]
    (current.phase :: periodicStrip.motif.length ::
      Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates)
    (getCost 3 values) restPhase

theorem flatPackedCenterBaseArguments
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits Code.flatPackedCenterBaseArgumentsCode
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      (Code.flatPackedCenterCandidateInput periodicStrip current cell)
      (flatPackedCenterBaseArgumentsCost periodicStrip current next valid
        processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have restWord := prepend (get 5 values) (drop 9 values)
  have restY := prepend
    (flatPackedTransitionCellField (1 : Fin 2) periodicStrip current next valid
      processed cell remaining split) restWord
  have restX := prepend
    (flatPackedTransitionCellField (0 : Fin 2) periodicStrip current next valid
      processed cell remaining split) restY
  have restLength := prepend (get 4 values) restX
  have restPhase := prepend (get 6 values) restLength
  have result := prepend (get 3 values) restPhase
  simpa [Code.flatPackedCenterBaseArgumentsCode,
    flatPackedCenterBaseArgumentsCost,
    Code.flatPackedCenterCandidateInput,
    Code.flatPackedTransitionScanState,
    PeriodicStripFlatEncoding.cellFields, prependCost, values] using result

def flatPackedCenterBaseAtCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  flatPackedCenterBaseValidCost tromino periodicStrip current cell +
    flatPackedCenterBaseArgumentsCost periodicStrip current next valid
      processed cell

theorem flatPackedCenterBaseAt
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedCenterBaseAtCode tromino)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(flatPackedCenterBaseBool tromino periodicStrip current cell).toNat]
      (flatPackedCenterBaseAtCost tromino periodicStrip current next valid
        processed cell) := by
  simpa [Code.flatPackedCenterBaseAtCode, flatPackedCenterBaseAtCost,
    flatPackedCenterBaseBool] using
    comp
      (flatPackedCenterBaseValid tromino periodicStrip wellFormed current cell)
      (flatPackedCenterBaseArguments periodicStrip current next valid
        processed cell remaining split)

def flatPackedCenterUpdatedValidCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  boolAndCost values valid.toNat
    (flatPackedCenterBaseBool tromino periodicStrip current cell).toNat
    (getCost 0 values)
    (flatPackedCenterBaseAtCost tromino periodicStrip current next valid
      processed cell)

theorem flatPackedCenterUpdatedValid
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedCenterUpdatedValidCode tromino)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(valid && flatPackedCenterBaseBool tromino periodicStrip current cell).toNat]
      (flatPackedCenterUpdatedValidCost tromino periodicStrip current
        next valid processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have combined := boolAnd (get 0 values)
    (flatPackedCenterBaseAt tromino periodicStrip wellFormed current next valid
      processed cell remaining split)
  cases valid <;>
    cases normalized :
      flatPackedCenterBaseBool tromino periodicStrip current cell <;>
    simpa [Code.flatPackedCenterUpdatedValidCode,
      flatPackedCenterUpdatedValidCost, values,
      Code.flatPackedTransitionScanState, normalized] using combined

def flatPackedCenterIndexCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  succCost [processed.length] + getCost 1 values

theorem flatPackedCenterIndex
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) :
    EvaluatorCodeFits (Code.succ.comp (Code.get 1))
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [processed.length + 1]
      (flatPackedCenterIndexCost periodicStrip current next valid
        processed) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [flatPackedCenterIndexCost, values,
    Code.flatPackedTransitionScanState, Nat.add_comm] using
    comp (succ_named [processed.length]) (get 1 values)

def flatPackedCenterIndexAndRestCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  prependCost values [processed.length + 1] (values.drop 2)
    (flatPackedCenterIndexCost periodicStrip current next valid
      processed) (dropCost 2 values)

theorem flatPackedCenterIndexAndRest
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    EvaluatorCodeFits
      (Code.prepend (Code.succ.comp (Code.get 1)) (Code.drop 2)) values
      ((processed.length + 1) :: values.drop 2)
      (flatPackedCenterIndexAndRestCost periodicStrip current next valid
        processed) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [flatPackedCenterIndexAndRestCost, values, prependCost] using
    prepend (flatPackedCenterIndex periodicStrip current next valid
      processed) (drop 2 values)

def flatPackedCenterStepCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let rest := (processed.length + 1) :: values.drop 2
  prependCost values
    [(valid && flatPackedCenterBaseBool tromino periodicStrip current cell).toNat]
    rest
    (flatPackedCenterUpdatedValidCost tromino periodicStrip current next
      valid processed cell)
    (flatPackedCenterIndexAndRestCost periodicStrip current next valid
      processed)

theorem flatPackedCenterStep
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedCenterStepCode tromino)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && flatPackedCenterBaseBool tromino periodicStrip current cell)
        (processed.length + 1))
      (flatPackedCenterStepCost tromino periodicStrip current next valid
        processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have fitted := prepend
    (flatPackedCenterUpdatedValid tromino periodicStrip wellFormed current next
      valid processed cell remaining split)
    (flatPackedCenterIndexAndRest periodicStrip current next valid
      processed)
  simpa [Code.flatPackedCenterStepCode,
    flatPackedCenterStepCost, values,
    Code.flatPackedTransitionScanState, prependCost] using fitted

def flatPackedCenterBodySuccCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remainingCount : Nat) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  flatCountdownBodyCost (fun _ =>
      Code.flatPackedTransitionScanState periodicStrip current next
        (valid && flatPackedCenterBaseBool tromino periodicStrip current cell)
        (processed.length + 1))
    (fun _ => flatPackedCenterStepCost tromino periodicStrip current next
      valid processed cell)
    (remainingCount + 1) values

theorem flatPackedCenterBodySucc
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    let output := Code.flatPackedTransitionScanState periodicStrip current next
      (valid && flatPackedCenterBaseBool tromino periodicStrip current cell)
      (processed.length + 1)
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.flatPackedCenterStepCode tromino))
      ((remaining.length + 1) :: values)
      (flatCountdownOutput (fun _ => output) (remaining.length + 1) values)
      (flatPackedCenterBodySuccCost tromino periodicStrip current next
        valid processed cell remaining.length) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (valid && flatPackedCenterBaseBool tromino periodicStrip current cell)
    (processed.length + 1)
  have transformed := comp
    (flatPackedCenterStep tromino periodicStrip wellFormed current next valid
      processed cell remaining split)
    (tail_named (remaining.length :: values))
  have payloadResult := prepend (head (remaining.length :: values)) transformed
  have branch := prepend (one (remaining.length :: values)) payloadResult
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedCenterBodySuccCost, flatCountdownBodyCost,
    flatCountdownSuccBranchCost, values, output, prependCost, Code.prepend] using
    EvaluatorCodeFits.case_succ
      (zeroBranch := Code.zero')
      (values := (remaining.length + 1) :: values)
      (predecessor := remaining.length) (by rfl) branch

def flatPackedCenterBodyZeroCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  flatCountdownBodyCost (fun _ => values) (fun _ => 0) 0 values

theorem flatPackedCenterBodyZero
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.flatPackedCenterStepCode tromino))
      (0 :: values) (flatCountdownOutput (fun _ => values) 0 values)
      (flatPackedCenterBodyZeroCost periodicStrip current next valid
        processed) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedCenterBodyZeroCost, flatCountdownBodyCost, values,
    zeroPrimeCost] using
    EvaluatorCodeFits.case_zero
      (successorBranch :=
        .cons Code.one
          (.cons Code.head
            ((Code.flatPackedCenterStepCode tromino).comp Code.tail)))
      (values := 0 :: values) (by rfl) (zero'_named values)

def flatPackedCenterFlatCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    Bool → List Cell → List Cell → Nat
  | valid, processed, [] =>
      flatPackedCenterBodyZeroCost periodicStrip current next valid
        processed
  | valid, processed, cell :: remaining =>
      let nextValid :=
        valid && flatPackedCenterBaseBool tromino periodicStrip current cell
      flatPackedCenterBodySuccCost tromino periodicStrip current next
          valid processed cell remaining.length +
        flatPackedCenterFlatCost tromino periodicStrip current next
          nextValid (processed ++ [cell]) remaining

theorem flatPackedCenterResultSpace_le_cost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    encodedListSpace
        (Code.flatPackedTransitionScanState periodicStrip current next
          (valid && remaining.all fun cell =>
            flatPackedCenterBaseBool tromino periodicStrip current cell)
          periodicStrip.motif.length) ≤
      flatPackedCenterFlatCost tromino periodicStrip current next valid
        processed remaining := by
  induction remaining generalizing valid processed with
  | nil =>
      have motifEq : periodicStrip.motif = processed := by simpa using split
      have output := (flatPackedCenterBodyZero tromino periodicStrip
        current next valid processed).output_space
      simpa [flatCountdownOutput, flatPackedCenterFlatCost, motifEq,
        Code.flatPackedTransitionScanState] using
        (listCodeEncodedListSpace_tail_le
          (0 :: Code.flatPackedTransitionScanState periodicStrip current next
            valid processed.length)).trans output
  | cons cell remaining induction =>
      let nextValid :=
        valid && flatPackedCenterBaseBool tromino periodicStrip current cell
      let nextProcessed := processed ++ [cell]
      have nextSplit : periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have tail := induction nextValid nextProcessed nextSplit
      simpa [flatPackedCenterFlatCost, nextValid, nextProcessed,
        Bool.and_assoc] using tail.trans (Nat.le_add_left _ _)

theorem flatPackedCenterFlat
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedCenterStepCode tromino))
      (remaining.length ::
        Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && remaining.all fun cell =>
          flatPackedCenterBaseBool tromino periodicStrip current cell)
        periodicStrip.motif.length)
      (flatPackedCenterFlatCost tromino periodicStrip current next valid
        processed remaining) where
  input_space := by
    cases remaining with
    | nil =>
        exact (flatPackedCenterBodyZero tromino periodicStrip current next
          valid processed).input_space
    | cons cell remaining =>
        have headSplit : periodicStrip.motif =
            processed ++ cell :: remaining := split
        exact (flatPackedCenterBodySucc tromino periodicStrip wellFormed
          current next valid processed cell remaining headSplit).input_space.trans (by
            simp [flatPackedCenterFlatCost])
  output_space := flatPackedCenterResultSpace_le_cost tromino
    periodicStrip current next valid processed remaining split
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction remaining generalizing valid processed with
    | nil =>
        let values := Code.flatPackedTransitionScanState periodicStrip current
          next valid processed.length
        have motifEq : periodicStrip.motif = processed := by simpa using split
        have body := flatPackedCenterBodyZero tromino periodicStrip
          current next valid processed
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    (Code.flatPackedCenterStepCode tromino))
                  continuation)
                (flatCountdownOutput (fun _ => values) 0 values)) := by
          apply EvaluatorExecutionFits.ret_fix_zero
          · rfl
          · simp only [continuationSpace_fix]
            have output := body.output_space
            simp only [flatPackedCenterFlatCost] at budget
            simp only [values] at *
            omega
          · simpa [flatCountdownOutput, values, motifEq,
              Code.flatPackedTransitionScanState] using after
        exact body.call
          (.fix
            (Code.flatCountdownBody
              (Code.flatPackedCenterStepCode tromino))
            continuation)
          bound
          (by
            simp only [continuationSpace_fix,
              flatPackedCenterFlatCost] at *
            exact budget)
          fixedAfter
    | cons cell remaining induction =>
        let nextValid :=
          valid && flatPackedCenterBaseBool tromino periodicStrip current cell
        let nextProcessed := processed ++ [cell]
        let values := Code.flatPackedTransitionScanState periodicStrip current
          next valid processed.length
        let output := Code.flatPackedTransitionScanState periodicStrip current
          next nextValid (processed.length + 1)
        have headSplit : periodicStrip.motif =
            processed ++ cell :: remaining := by
          simpa [List.append_assoc] using split
        have nextSplit : periodicStrip.motif =
            nextProcessed ++ remaining := by
          simpa [nextProcessed, List.append_assoc] using split
        have body := flatPackedCenterBodySucc tromino periodicStrip wellFormed
          current next valid processed cell remaining headSplit
        have recursiveBudget :
            flatPackedCenterFlatCost tromino periodicStrip current next
                nextValid nextProcessed remaining +
              continuationSpace continuation ≤ bound := by
          have raw : flatPackedCenterFlatCost tromino periodicStrip
                current next
                (valid && flatPackedCenterBaseBool tromino periodicStrip current cell)
                (processed ++ [cell]) remaining +
              continuationSpace continuation ≤ bound := by
            simp only [flatPackedCenterFlatCost] at budget
            omega
          simpa only [nextValid, nextProcessed] using raw
        have recursiveAfter :
            EvaluatorExecutionFits bound
              (.ret continuation
                (Code.flatPackedTransitionScanState periodicStrip current next
                  (nextValid && remaining.all fun tailCell =>
                    flatPackedCenterBaseBool tromino periodicStrip current tailCell)
                  periodicStrip.motif.length)) := by
          simpa [nextValid, Bool.and_assoc] using after
        have recursiveBody := induction nextValid nextProcessed nextSplit
          recursiveBudget recursiveAfter
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    (Code.flatPackedCenterStepCode tromino))
                  continuation)
                (flatCountdownOutput (fun _ => output)
                  (remaining.length + 1) values)) := by
          apply EvaluatorExecutionFits.ret_fix_succ
          · simp [flatCountdownOutput, output, nextValid]
          · simp only [continuationSpace_fix]
            have outputSpace := body.output_space
            simp only [flatPackedCenterFlatCost] at budget
            simp only [values, output, nextValid, nextProcessed] at *
            omega
          · simpa [flatCountdownOutput, output, nextValid,
              nextProcessed] using recursiveBody
        exact body.call
          (.fix
            (Code.flatCountdownBody
              (Code.flatPackedCenterStepCode tromino))
            continuation)
          bound
          (by
            simp only [continuationSpace_fix]
            simp only [flatPackedCenterFlatCost] at budget
            omega)
          fixedAfter

/-! ## Native polynomial bounds -/

def flatPackedCenterContextUnit
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next) + 10

def flatPackedCenterAtUnit (values : List Nat) : Nat :=
  encodedListSpace values + 10

def flatPackedCenterContextCore
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  (10 ^ 1000) *
    (flatPackedCenterContextUnit periodicStrip current next) ^ 2

def flatPackedCenterBodySpaceBound
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  (10 ^ 1100) *
    (flatPackedCenterContextUnit periodicStrip current next) ^ 2

theorem flatPackedCenterContextCore_large
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) :
    1000000 * flatPackedCenterContextUnit periodicStrip current next +
        1000 ≤
      flatPackedCenterContextCore periodicStrip current next := by
  let unit := flatPackedCenterContextUnit periodicStrip current next
  have positive : 10 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  have squareDominates : unit ≤ unit ^ 2 := by nlinarith
  simp only [flatPackedCenterContextCore]
  change 1000000 * unit + 1000 ≤ _ * unit ^ 2
  omega

theorem flatPackedCenterScanUnit_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (index : Nat) (indexBound : index ≤ periodicStrip.motif.length) :
    flatPackedCenterAtUnit
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          index) ≤
      2 * flatPackedCenterContextUnit periodicStrip current next := by
  let context := Code.flatPackedTransitionContext periodicStrip current next
  have indexBits := listCodeEncodeNat_length_mono indexBound
  have motifMember : periodicStrip.motif.length ∈ context := by
    simp [context, Code.flatPackedTransitionContext]
  have motifSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length context motifMember
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases valid <;>
    simp [flatPackedCenterAtUnit,
      flatPackedCenterContextUnit,
      Code.flatPackedTransitionScanState,
      Code.flatPackedTransitionContext, context,
      encodedListSpace_cons, zeroBits, oneBits] at * <;>
    omega

theorem flatPackedCenterCandidateUnit_le_context
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterCandidateInputUnit periodicStrip current cell ≤
      16 * flatPackedCenterContextUnit periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip current
    next valid processed.length indexBound
  have valuesBound : encodedListSpace values + 10 ≤ 2 * unit := by
    simpa [values, unit, flatPackedCenterAtUnit] using scanUnit
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  have coordinates := flatPackedTransitionCoordinatesSpace_le periodicStrip
    current next valid processed.length
  have periodMember : periodicStrip.period ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have phaseMember : current.phase ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have lengthMember : periodicStrip.motif.length ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have wordMember : current.assignmentWord ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have periodSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.period values periodMember
  have phaseSpace := flatPackedTransitionScanMemberSpace_le
    current.phase values phaseMember
  have lengthSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length values lengthMember
  have wordSpace := flatPackedTransitionScanMemberSpace_le
    current.assignmentWord values wordMember
  change encodedListSpace
      (Code.flatPackedCenterCandidateInput periodicStrip current cell) + 10 ≤
    16 * unit
  simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace coordinates periodSpace phaseSpace lengthSpace wordSpace
  simp only [Code.flatPackedCenterCandidateInput, List.cons_append,
    List.nil_append, encodedListSpace_cons]
  simp only [values] at xSpace ySpace coordinates periodSpace phaseSpace lengthSpace wordSpace valuesBound
  omega

theorem flatPackedCenterBaseArgumentsCost_le_quadratic
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterBaseArgumentsCost periodicStrip current next valid
        processed cell ≤
      (10 ^ 100) *
        (flatPackedCenterContextUnit periodicStrip current next) ^ 2 := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip current
    next valid processed.length indexBound
  have scanSpace : encodedListSpace values + 1 ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have getBound : ∀ index : Nat, index ≤ 9 →
      getCost index values ≤ 200000 * unit := by
    intro index fixed
    have raw := listCodeGetCost_le_linear index values
    calc
      _ ≤ (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
      _ ≤ 100000 * (2 * unit) := by gcongr; omega
      _ = 200000 * unit := by ring
  have get3 := getBound 3 (by omega)
  have get4 := getBound 4 (by omega)
  have get5 := getBound 5 (by omega)
  have get6 := getBound 6 (by omega)
  have get9 := getBound 9 (by omega)
  have drop9 : dropCost 9 values ≤ 200000 * unit := by
    have raw : dropCost 9 values ≤ getCost 9 values := by
      simp only [getCost]
      omega
    exact raw.trans get9
  have fieldCoefficient :
      4 *
          100000000000000000000000000000000000000000000000000000000000000000 ≤
        10 ^ 80 := by native_decide
  have fieldBound (field : Fin 2) :
      flatPackedTransitionCellFieldCost field periodicStrip current next valid
          processed.length ≤ (10 ^ 80) * unit ^ 2 := by
    have raw := flatPackedTransitionCellFieldCost_le_core field periodicStrip
      current next valid processed.length
    have normalizationUnit : flatPackedNormalizationAtUnit values ≤
        2 * unit := by
      simpa [flatPackedNormalizationAtUnit, flatPackedCenterAtUnit,
        values, unit] using scanUnit
    calc
      _ ≤ 100000000000000000000000000000000000000000000000000000000000000000 *
          (flatPackedNormalizationAtUnit values) ^ 2 := by
        simpa [flatPackedNormalizationAtCoreBound, values] using raw
      _ ≤ 100000000000000000000000000000000000000000000000000000000000000000 *
          (2 * unit) ^ 2 := by gcongr
      _ = (4 *
          100000000000000000000000000000000000000000000000000000000000000000) *
            unit ^ 2 := by ring
      _ ≤ (10 ^ 80) * unit ^ 2 :=
        Nat.mul_le_mul_right (unit ^ 2) fieldCoefficient
  have fieldX := fieldBound (0 : Fin 2)
  have fieldY := fieldBound (1 : Fin 2)
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  have coordinatesSpace : encodedListSpace (values.drop 9) ≤
      encodedListSpace values := dynamicDropSpace_drop_le 9 values
  have periodMember : periodicStrip.period ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have phaseMember : current.phase ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have lengthMember : periodicStrip.motif.length ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have wordMember : current.assignmentWord ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have periodSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.period values periodMember
  have phaseSpace := flatPackedTransitionScanMemberSpace_le
    current.phase values phaseMember
  have lengthSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length values lengthMember
  have wordSpace := flatPackedTransitionScanMemberSpace_le
    current.assignmentWord values wordMember
  change flatPackedCenterBaseArgumentsCost periodicStrip current next valid
      processed cell ≤ (10 ^ 100) * unit ^ 2
  simp [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace periodSpace phaseSpace lengthSpace wordSpace
  simp [flatPackedCenterBaseArgumentsCost, prependCost,
    encodedListSpace_cons, encodedListSpace_nil]
  simp only [values] at *
  omega

theorem flatPackedCenterBaseAtCost_le_context_core
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterBaseAtCost tromino periodicStrip current next valid
        processed cell ≤
      flatPackedCenterContextCore periodicStrip current next := by
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let coefficient := flatPackedCenterBaseValidQuadraticCoefficient tromino
  have candidateUnit := flatPackedCenterCandidateUnit_le_context
    periodicStrip current next valid processed cell remaining split
  have baseCost : flatPackedCenterBaseValidCost tromino periodicStrip current
      cell ≤ 256 * coefficient * unit ^ 2 := by
    calc
      flatPackedCenterBaseValidCost tromino periodicStrip current cell ≤
          flatPackedCenterBaseValidSpaceBound tromino periodicStrip current
            cell := flatPackedCenterBaseValidCost_le_linear tromino
              periodicStrip current cell
      _ ≤ coefficient *
          (flatPackedCenterCandidateInputUnit periodicStrip current cell) ^ 2 :=
        flatPackedCenterBaseValidSpaceBound_le_quadratic tromino
          periodicStrip current cell
      _ ≤ coefficient * (16 * unit) ^ 2 := by gcongr
      _ = 256 * coefficient * unit ^ 2 := by ring
  have arguments := flatPackedCenterBaseArgumentsCost_le_quadratic
    periodicStrip current next valid processed cell remaining split
  have coefficientBound :
      256 * coefficient + 10 ^ 100 ≤ 10 ^ 1000 := by
    cases tromino <;> native_decide
  change flatPackedCenterBaseValidCost tromino periodicStrip current cell +
      flatPackedCenterBaseArgumentsCost periodicStrip current next valid
        processed cell ≤
    flatPackedCenterContextCore periodicStrip current next
  calc
    _ ≤ 256 * coefficient * unit ^ 2 + (10 ^ 100) * unit ^ 2 :=
      Nat.add_le_add baseCost arguments
    _ = (256 * coefficient + 10 ^ 100) * unit ^ 2 := by ring
    _ ≤ (10 ^ 1000) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficientBound
    _ = flatPackedCenterContextCore periodicStrip current next := by
      rfl

theorem flatPackedCenterGetCost_le_context_core
    (index : Nat) (fixed : index ≤ 9)
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    getCost index
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedCenterContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid scanIndex
  let unit := flatPackedCenterContextUnit periodicStrip current next
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid scanIndex indexBound
  have scanSpace : encodedListSpace values + 1 ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have raw := listCodeGetCost_le_linear index values
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have coefficient : 200000 ≤ 10 ^ 1000 := by native_decide
  calc
    getCost index values ≤
        (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
    _ ≤ 100000 * (2 * unit) := by
      gcongr
      omega
    _ = 200000 * unit := by ring
    _ ≤ 200000 * unit ^ 2 := Nat.mul_le_mul_left 200000 unitQuadratic
    _ ≤ (10 ^ 1000) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficient
    _ = flatPackedCenterContextCore periodicStrip current next := by
      rfl

theorem flatPackedCenterDropTwoCost_le_context_core
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    dropCost 2
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedCenterContextCore periodicStrip current next := by
  have whole := flatPackedCenterGetCost_le_context_core 2 (by omega)
    periodicStrip current next valid scanIndex indexBound
  have part : dropCost 2
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        scanIndex) ≤
    getCost 2
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        scanIndex) := by
    simp only [getCost]
    omega
  exact part.trans whole

theorem flatPackedCenterDropNineCost_le_context_core
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    dropCost 9
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedCenterContextCore periodicStrip current next := by
  have whole := flatPackedCenterGetCost_le_context_core 9 (by omega)
    periodicStrip current next valid scanIndex indexBound
  have part : dropCost 9
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        scanIndex) ≤
    getCost 9
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        scanIndex) := by
    simp only [getCost]
    omega
  exact part.trans whole

set_option maxHeartbeats 1000000 in
theorem flatPackedCenterUpdatedValidCost_le_context
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterUpdatedValidCost tromino periodicStrip current next
        valid processed cell ≤
      2000 * flatPackedCenterContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let core := flatPackedCenterContextCore periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid processed.length indexBound
  have scanSpace : encodedListSpace values + 10 ≤ 2 * unit := by
    simpa [values, unit, flatPackedCenterAtUnit] using scanUnit
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  have squareDominates : unit ≤ unit ^ 2 := by nlinarith
  have coreLarge : 2 * unit + 1 ≤ core := by
    simp only [core, flatPackedCenterContextCore]
    change 2 * unit + 1 ≤ _ * unit ^ 2
    omega
  have valuesBound : encodedListSpace values ≤ core := by
    omega
  have get0 := flatPackedCenterGetCost_le_context_core 0 (by omega)
    periodicStrip current next valid processed.length indexBound
  have atCost := flatPackedCenterBaseAtCost_le_context_core tromino
    periodicStrip current next valid processed cell remaining split
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBound : (Computability.encodeNat values.headI).length ≤ core := by
    have localBound : (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans valuesBound
  have successor := listCodeEncodeNat_succ_length_le values.headI
  have valuesPlus : encodedListSpace values + 1 ≤ core := by
    have localBound : encodedListSpace values + 1 ≤ 2 * unit + 1 := by
      omega
    exact localBound.trans coreLarge
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ core := by
    have localBound :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using successor
    have headPlus : (Computability.encodeNat values.headI).length + 1 ≤
        encodedListSpace values + 1 := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans (headPlus.trans valuesPlus)
  have positive : 1 ≤ core := by
    omega
  have wrapped := boolAndCost_le_budget values valid.toNat
    (flatPackedCenterBaseBool tromino periodicStrip current cell).toNat
    (getCost 0 values)
    (flatPackedCenterBaseAtCost tromino periodicStrip current next valid
      processed cell)
    core (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
      headSuccessorBound (by simpa [values, core] using get0)
      (by simpa [core] using atCost) positive
  have exact : flatPackedCenterUpdatedValidCost tromino periodicStrip
      current next valid processed cell ≤ 1000 * (core + 1) := by
    simpa [flatPackedCenterUpdatedValidCost, values] using wrapped
  exact exact.trans (by
    omega)

theorem flatPackedCenterIndexCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell)
    (processedBound : processed.length ≤ periodicStrip.motif.length) :
    flatPackedCenterIndexCost periodicStrip current next valid
        processed ≤
      2 * flatPackedCenterContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let core := flatPackedCenterContextCore periodicStrip current next
  have get1 := flatPackedCenterGetCost_le_context_core 1 (by omega)
    periodicStrip current next valid processed.length processedBound
  have selected := flatMotifIndexSelectedSpace_le 1 values
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have selectedSpace : encodedListSpace [processed.length] ≤ 2 * unit := by
    have valueEq : values[1]?.getD 0 = processed.length := by
      simp [values, Code.flatPackedTransitionScanState]
    rw [valueEq] at selected
    simp only [flatPackedCenterAtUnit] at scanUnit
    exact selected.trans (by
      simp only [values, unit]
      omega)
  have successorRaw := succCost_le [processed.length]
  have coreLarge := flatPackedCenterContextCore_large periodicStrip
    current next
  have successor : succCost [processed.length] ≤ core := by
    calc
      succCost [processed.length] ≤
          100 * (encodedListSpace [processed.length] + 1) := successorRaw
      _ ≤ 100 * (2 * unit + 1) := by gcongr
      _ ≤ core := by omega
  change succCost [processed.length] + getCost 1 values ≤ 2 * core
  change getCost 1 values ≤ core at get1
  omega

theorem flatPackedCenterIndexAndRestCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) (cell : Cell)
    (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterIndexAndRestCost periodicStrip current next valid
        processed ≤
      4 * flatPackedCenterContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let core := flatPackedCenterContextCore periodicStrip current next
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have indexCost := flatPackedCenterIndexCost_le_context periodicStrip
    current next valid processed processedBound
  have dropBound := flatPackedCenterDropTwoCost_le_context_core
    periodicStrip current next valid processed.length processedBound
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have nextScanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid (processed.length + 1) nextBound
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have fieldSpace : encodedListSpace [processed.length + 1] ≤
      2 * unit := by
    have indexBits := listCodeEncodeNat_length_mono nextBound
    have motifMember : periodicStrip.motif.length ∈
        Code.flatPackedTransitionContext periodicStrip current next := by
      simp [Code.flatPackedTransitionContext]
    have motifSpace := flatPackedTransitionScanMemberSpace_le
      periodicStrip.motif.length
      (Code.flatPackedTransitionContext periodicStrip current next) motifMember
    simp only [encodedListSpace_cons, encodedListSpace_nil] at motifSpace ⊢
    simp [unit, flatPackedCenterContextUnit] at motifSpace ⊢
    omega
  have outputSpace : encodedListSpace
      ((processed.length + 1) :: values.drop 2) ≤ 2 * unit := by
    have tail := listCodeEncodedListSpace_tail_le
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        (processed.length + 1))
    have outputEq : (processed.length + 1) :: values.drop 2 =
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          (processed.length + 1)).tail := by
      simp [values, Code.flatPackedTransitionScanState]
    rw [outputEq]
    exact tail.trans (by
      simp only [flatPackedCenterAtUnit] at nextScanUnit
      simp only [unit]
      omega)
  have raw := listCodePrependCost_le_of values [processed.length + 1]
    (values.drop 2)
    (flatPackedCenterIndexCost periodicStrip current next valid
      processed) (EvaluatorCodeFits.dropCost 2 values) (2 * unit) valuesSpace fieldSpace (by
        simpa only [List.headI_cons] using outputSpace)
  have coreLarge := flatPackedCenterContextCore_large periodicStrip
    current next
  have overhead : 6 * unit + 2 ≤ core := by omega
  change prependCost values [processed.length + 1] (values.drop 2)
    (flatPackedCenterIndexCost periodicStrip current next valid
      processed) (EvaluatorCodeFits.dropCost 2 values) ≤ 4 * core
  change flatPackedCenterIndexCost periodicStrip current next valid
    processed ≤ 2 * core at indexCost
  change EvaluatorCodeFits.dropCost 2 values ≤ core at dropBound
  omega

theorem flatPackedCenterStepCost_le_context
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterStepCost tromino periodicStrip current next valid
        processed cell ≤
      2005 * flatPackedCenterContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let core := flatPackedCenterContextCore periodicStrip current next
  let nextValid := valid && flatPackedCenterBaseBool tromino periodicStrip current cell
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have updated := flatPackedCenterUpdatedValidCost_le_context tromino
    periodicStrip current next valid processed cell remaining split
  have rest := flatPackedCenterIndexAndRestCost_le_context periodicStrip
    current next valid processed cell remaining split
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have nextScanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next nextValid (processed.length + 1) nextBound
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have fieldSpace : encodedListSpace [nextValid.toNat] ≤ 2 * unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases nextValid with
    | false =>
        simp [unit, flatPackedCenterContextUnit,
          encodedListSpace_cons, zeroBits]
        omega
    | true =>
        simp [unit, flatPackedCenterContextUnit,
          encodedListSpace_cons, oneBits]
  have outputSpace : encodedListSpace
      (Code.flatPackedTransitionScanState periodicStrip current next nextValid
        (processed.length + 1)) ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at nextScanUnit
    simp only [unit]
    omega
  have raw := listCodePrependCost_le_of values [nextValid.toNat]
    ((processed.length + 1) :: values.drop 2)
    (flatPackedCenterUpdatedValidCost tromino periodicStrip current next
      valid processed cell)
    (flatPackedCenterIndexAndRestCost periodicStrip current next valid
      processed) (2 * unit) valuesSpace fieldSpace (by
        simpa [nextValid, values, Code.flatPackedTransitionScanState] using
          outputSpace)
  have coreLarge := flatPackedCenterContextCore_large periodicStrip
    current next
  have overhead : 6 * unit + 2 ≤ core := by omega
  change prependCost values [nextValid.toNat]
      ((processed.length + 1) :: values.drop 2)
      (flatPackedCenterUpdatedValidCost tromino periodicStrip current next
        valid processed cell)
      (flatPackedCenterIndexAndRestCost periodicStrip current next valid
        processed) ≤ 2005 * core
  change flatPackedCenterUpdatedValidCost tromino periodicStrip current
    next valid processed cell ≤ 2000 * core at updated
  change flatPackedCenterIndexAndRestCost periodicStrip current next
    valid processed ≤ 4 * core at rest
  omega

theorem flatPackedCenterBodySuccCost_le_context
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedCenterBodySuccCost tromino periodicStrip current next valid
        processed cell remaining.length ≤
      flatPackedCenterBodySpaceBound periodicStrip current next := by
  let payload := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let nextValid := valid && flatPackedCenterBaseBool tromino periodicStrip current cell
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    nextValid (processed.length + 1)
  let values := remaining.length :: payload
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let core := flatPackedCenterContextCore periodicStrip current next
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have remainingBound : remaining.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
    omega
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  have payloadUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have outputUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next nextValid (processed.length + 1) nextBound
  have payloadSpace : encodedListSpace payload ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at payloadUnit
    simp only [payload, unit]
    omega
  have outputSpace : encodedListSpace output ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at outputUnit
    simp only [output, unit]
    omega
  have countBits := listCodeEncodeNat_length_mono remainingBound
  have motifMember : periodicStrip.motif.length ∈
      Code.flatPackedTransitionContext periodicStrip current next := by
    simp [Code.flatPackedTransitionContext]
  have motifSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length
    (Code.flatPackedTransitionContext periodicStrip current next) motifMember
  have countSpace : encodedListSpace [remaining.length] ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at motifSpace ⊢
    simp [unit, flatPackedCenterContextUnit] at motifSpace ⊢
    omega
  have valuesSpace : encodedListSpace values ≤ 3 * unit := by
    simp only [values, encodedListSpace_cons]
    simp only [encodedListSpace_cons, encodedListSpace_nil] at countSpace
    omega
  have countOutputSpace : encodedListSpace (remaining.length :: output) ≤
      3 * unit := by
    simp only [encodedListSpace_cons]
    simp only [encodedListSpace_cons, encodedListSpace_nil] at countSpace
    omega
  have taggedOutputSpace : encodedListSpace
      (1 :: remaining.length :: output) ≤ 4 * unit := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp only [encodedListSpace_cons, oneBits]
    simp only [encodedListSpace_cons] at countOutputSpace
    omega
  have coreLarge := flatPackedCenterContextCore_large periodicStrip
    current next
  have tailRaw := listCodeTailCost_le_linear values
  have tailBound : tailCost values ≤ core := by
    calc
      tailCost values ≤ 3 * (encodedListSpace values + 1) := tailRaw
      _ ≤ 3 * (3 * unit + 1) := by gcongr
      _ ≤ core := by omega
  have headRaw := headCost_le values
  have headBound : headCost values ≤ core := by
    calc
      headCost values ≤ 1000 * (encodedListSpace values + 1) := headRaw
      _ ≤ 1000 * (3 * unit + 1) := by gcongr
      _ ≤ core := by omega
  have oneRaw := flatLookupOneCost_le_linear values
  have oneBound : oneCost values ≤ core := by
    calc
      oneCost values ≤ 20000 * (encodedListSpace values + 1) := oneRaw
      _ ≤ 20000 * (3 * unit + 1) := by gcongr
      _ ≤ core := by omega
  have step := flatPackedCenterStepCost_le_context tromino periodicStrip
    current next valid processed cell remaining split
  change flatPackedCenterStepCost tromino periodicStrip current next valid
    processed cell ≤ 2005 * core at step
  let transformedCost :=
    flatPackedCenterStepCost tromino periodicStrip current next valid
      processed cell + tailCost values
  have transformedBound : transformedCost ≤ 2006 * core := by
    simp only [transformedCost]
    omega
  let payloadCost := prependCost values [remaining.length] output
    (headCost values) transformedCost
  have payloadRaw := listCodePrependCost_le_of values [remaining.length] output
    (headCost values) transformedCost (4 * unit)
    (valuesSpace.trans (by omega)) (countSpace.trans (by omega))
    (by simpa only [List.headI_cons] using countOutputSpace.trans (by omega))
  have overhead : 12 * unit + 2 ≤ core := by omega
  have payloadBound : payloadCost ≤ 2008 * core := by
    simp only [payloadCost]
    omega
  have branchRaw := listCodePrependCost_le_of values [1]
    (remaining.length :: output) (oneCost values) payloadCost (4 * unit)
    (valuesSpace.trans (by omega)) (by
      have oneBits : (Computability.encodeNat 1).length = 1 := rfl
      simp [encodedListSpace_cons, oneBits, unit,
        flatPackedCenterContextUnit]
      omega)
    (by simpa only [List.headI_cons] using taggedOutputSpace)
  have branchBound : flatCountdownSuccBranchCost (fun _ => output)
      (fun _ => flatPackedCenterStepCost tromino periodicStrip current
        next valid processed cell) remaining.length payload ≤
      2010 * core := by
    change prependCost values [1] (remaining.length :: output)
      (oneCost values) payloadCost ≤ 2010 * core
    omega
  have bodyBound : flatPackedCenterBodySuccCost tromino periodicStrip
      current next valid processed cell remaining.length ≤ 2011 * core := by
    simp only [flatPackedCenterBodySuccCost, flatCountdownBodyCost]
    change flatCountdownSuccBranchCost (fun _ => output)
        (fun _ => flatPackedCenterStepCost tromino periodicStrip current
          next valid processed cell) remaining.length payload +
      encodedListSpace ((remaining.length + 1) :: payload) +
      encodedListSpace (1 :: remaining.length :: output) + 1 ≤ 2011 * core
    have remainingSucc := listCodeEncodeNat_succ_length_le remaining.length
    have remainingSucc' :
        (Computability.encodeNat (remaining.length + 1)).length ≤
          (Computability.encodeNat remaining.length).length + 1 := by
      simpa [Nat.succ_eq_add_one] using remainingSucc
    have inputSpace : encodedListSpace ((remaining.length + 1) :: payload) ≤
        4 * unit := by
      simp only [encodedListSpace_cons]
      simp only [encodedListSpace_cons, encodedListSpace_nil] at countSpace
      omega
    have bodyOverhead :
        encodedListSpace ((remaining.length + 1) :: payload) +
            encodedListSpace (1 :: remaining.length :: output) + 1 ≤
          core := by
      omega
    omega
  calc
    flatPackedCenterBodySuccCost tromino periodicStrip current next valid
        processed cell remaining.length ≤ 2011 * core := bodyBound
    _ ≤ flatPackedCenterBodySpaceBound periodicStrip current next := by
      have coefficient : 2011 * (10 ^ 1000) ≤ 10 ^ 1100 := by
        native_decide
      change 2011 * ((10 ^ 1000) * unit ^ 2) ≤
        (10 ^ 1100) * unit ^ 2
      calc
        _ = (2011 * (10 ^ 1000)) * unit ^ 2 :=
          (Nat.mul_assoc 2011 (10 ^ 1000) (unit ^ 2)).symm
        _ ≤ (10 ^ 1100) * unit ^ 2 :=
          Nat.mul_le_mul_right (unit ^ 2) coefficient

theorem flatPackedCenterBodyZeroCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell)
    (processedBound : processed.length ≤ periodicStrip.motif.length) :
    flatPackedCenterBodyZeroCost periodicStrip current next valid
        processed ≤
      flatPackedCenterBodySpaceBound periodicStrip current next := by
  let payload := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedCenterContextUnit periodicStrip current next
  have scanUnit := flatPackedCenterScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have payloadSpace : encodedListSpace payload ≤ 2 * unit := by
    simp only [flatPackedCenterAtUnit] at scanUnit
    simp only [payload, unit]
    omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have coreLarge := flatPackedCenterContextCore_large periodicStrip
    current next
  have coreToBody : flatPackedCenterContextCore periodicStrip current
      next ≤ flatPackedCenterBodySpaceBound periodicStrip current
      next := by
    have coefficient : 10 ^ 1000 ≤ 10 ^ 1100 := by native_decide
    change (10 ^ 1000) * unit ^ 2 ≤ (10 ^ 1100) * unit ^ 2
    exact Nat.mul_le_mul_right (unit ^ 2) coefficient
  change zeroPrimeCost payload + encodedListSpace (0 :: payload) +
      encodedListSpace (0 :: payload) + 1 ≤
    flatPackedCenterBodySpaceBound periodicStrip current next
  have localBound : zeroPrimeCost payload + encodedListSpace (0 :: payload) +
      encodedListSpace (0 :: payload) + 1 ≤
      flatPackedCenterContextCore periodicStrip current next := by
    simp [zeroPrimeCost, encodedListSpace_cons, zeroBits]
    omega
  exact localBound.trans coreToBody

theorem flatPackedCenterFlatCost_le_body_mul
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    flatPackedCenterFlatCost tromino periodicStrip current next valid
        processed remaining ≤
      flatPackedCenterBodySpaceBound periodicStrip current next *
        (remaining.length + 1) := by
  induction remaining generalizing valid processed with
  | nil =>
      have processedBound : processed.length ≤
          periodicStrip.motif.length := by
        have lengths := congrArg List.length split
        simp only [List.append_nil] at lengths
        omega
      simpa [flatPackedCenterFlatCost] using
        flatPackedCenterBodyZeroCost_le_context periodicStrip current
          next valid processed processedBound
  | cons cell remaining induction =>
      let nextValid :=
        valid && flatPackedCenterBaseBool tromino periodicStrip current cell
      let nextProcessed := processed ++ [cell]
      have headSplit : periodicStrip.motif =
          processed ++ cell :: remaining := by
        simpa [List.append_assoc] using split
      have nextSplit : periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have body := flatPackedCenterBodySuccCost_le_context tromino
        periodicStrip current next valid processed cell remaining headSplit
      have tail := induction nextValid nextProcessed nextSplit
      simp only [flatPackedCenterFlatCost, List.length_cons]
      simp only [nextValid, nextProcessed] at tail
      nlinarith

theorem flatPackedCenterMotifLength_le_contextUnit
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) :
    periodicStrip.motif.length + 1 ≤
      flatPackedCenterContextUnit periodicStrip current next := by
  have lengthBound := list_length_le_encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next)
  have contextLength :
      (Code.flatPackedTransitionContext periodicStrip current next).length =
        7 + 2 * periodicStrip.motif.length := by
    simp [Code.flatPackedTransitionContext,
      PeriodicStripFlatEncoding.cellFields, List.length_flatMap]
    omega
  rw [contextLength] at lengthBound
  simp [flatPackedCenterContextUnit]
  omega

theorem flatPackedCenterFlatCost_le_cubic
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedCenterFlatCost tromino periodicStrip current next true []
        periodicStrip.motif ≤
      (10 ^ 1100) *
        (flatPackedCenterContextUnit periodicStrip current next) ^ 3 := by
  have additive := flatPackedCenterFlatCost_le_body_mul tromino
    periodicStrip current next true [] periodicStrip.motif (by simp)
  have length := flatPackedCenterMotifLength_le_contextUnit
    periodicStrip current next
  calc
    flatPackedCenterFlatCost tromino periodicStrip current next true []
        periodicStrip.motif ≤
      flatPackedCenterBodySpaceBound periodicStrip current next *
        (periodicStrip.motif.length + 1) := additive
    _ ≤ flatPackedCenterBodySpaceBound periodicStrip current next *
        flatPackedCenterContextUnit periodicStrip current next := by
      gcongr
    _ = _ := by
      change (10 ^ 1100) *
          (flatPackedCenterContextUnit periodicStrip current next) ^ 2 *
            flatPackedCenterContextUnit periodicStrip current next =
        (10 ^ 1100) *
          (flatPackedCenterContextUnit periodicStrip current next) ^ 3
      have cube :
          (flatPackedCenterContextUnit periodicStrip current next) ^ 3 =
            (flatPackedCenterContextUnit periodicStrip current next) ^ 2 *
              flatPackedCenterContextUnit periodicStrip current next := by
        exact pow_succ _ 2
      rw [cube]
      rw [Nat.mul_assoc]

theorem flatPackedCenterFlatBounded
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedCenterStepCode tromino))
      (remaining.length ::
        Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && remaining.all fun cell =>
          flatPackedCenterBaseBool tromino periodicStrip current cell)
        periodicStrip.motif.length)
      (flatPackedCenterBodySpaceBound periodicStrip current next *
        (remaining.length + 1)) :=
  (flatPackedCenterFlat tromino periodicStrip wellFormed current next valid
    processed remaining split).mono
      (flatPackedCenterFlatCost_le_body_mul tromino periodicStrip current
        next valid processed remaining split)

/-! ## Complete tromino wrapper -/

def flatPackedCenterLoopInputCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let zeroAndContext := prependCost values [0] values
    (zeroCost values) (idCost values)
  let validIndexAndContext := prependCost values [1] (0 :: values)
    (oneCost values) zeroAndContext
  prependCost values [periodicStrip.motif.length] (1 :: 0 :: values)
    (getCost 2 values) validIndexAndContext

theorem flatPackedCenterLoopInput
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedCenterLoopInputCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      (periodicStrip.motif.length ::
        Code.flatPackedTransitionScanState periodicStrip current next true 0)
      (flatPackedCenterLoopInputCost periodicStrip current next) := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  have fitted := prepend (get 2 values)
    (prepend (one values) (prepend (zero values) (id values)))
  simpa [Code.flatPackedCenterLoopInputCode,
    Code.flatPackedNormalizationLoopInputCode,
    flatPackedCenterLoopInputCost, values, prependCost,
    Code.flatPackedTransitionContext,
    Code.flatPackedTransitionScanState] using fitted

theorem flatPackedCenterLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedCenterLoopInputCost periodicStrip current next ≤
      100000 *
        flatPackedCenterContextUnit periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let zeroAndContext := prependCost values [0] values
    (zeroCost values) (idCost values)
  let validIndexAndContext := prependCost values [1] (0 :: values)
    (oneCost values) zeroAndContext
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp [unit, flatPackedCenterContextUnit, values]
    omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have zeroSpace : encodedListSpace [0] ≤ 2 * unit := by
    simp [encodedListSpace_cons, encodedListSpace_nil, zeroBits]
    omega
  have oneSpace : encodedListSpace [1] ≤ 2 * unit := by
    simp [encodedListSpace_cons, encodedListSpace_nil, oneBits]
    omega
  have zeroAndContextSpace : encodedListSpace (0 :: values) ≤ 2 * unit := by
    simp [encodedListSpace_cons, zeroBits, unit,
      flatPackedCenterContextUnit, values]
    omega
  have validIndexAndContextSpace :
      encodedListSpace (1 :: 0 :: values) ≤ 2 * unit := by
    simp [encodedListSpace_cons, zeroBits, oneBits, unit,
      flatPackedCenterContextUnit, values]
    omega
  have motifMember : periodicStrip.motif.length ∈ values := by
    simp [values, Code.flatPackedTransitionContext]
  have motifSpace : encodedListSpace [periodicStrip.motif.length] ≤
      2 * unit :=
    (flatPackedTransitionScanMemberSpace_le periodicStrip.motif.length values
      motifMember).trans valuesSpace
  have finalSpace : encodedListSpace
      (periodicStrip.motif.length :: 1 :: 0 :: values) ≤ 2 * unit := by
    have prefixBound := flatLookupEncodedListSpace_prefix_le
      [periodicStrip.motif.length] (1 :: 0 :: values)
    have fieldInValues := flatPackedTransitionScanMemberSpace_le
      periodicStrip.motif.length values motifMember
    simp only [encodedListSpace_cons, encodedListSpace_nil] at fieldInValues
    simp [encodedListSpace_cons, zeroBits, oneBits, unit,
      flatPackedCenterContextUnit, values] at prefixBound fieldInValues ⊢
    omega
  have identityRaw := flatLookupIdCost_le_linear values
  have identity : idCost values ≤ 10 * unit := by
    exact identityRaw.trans (by
      simp [unit, flatPackedCenterContextUnit, values])
  have zeroRaw := listCodeZeroCost_le_linear values
  have zero : zeroCost values ≤ 10000 * unit := by
    exact zeroRaw.trans (by
      simp [unit, flatPackedCenterContextUnit, values])
  have oneRaw := flatLookupOneCost_le_linear values
  have one : oneCost values ≤ 20000 * unit := by
    exact oneRaw.trans (by
      simp [unit, flatPackedCenterContextUnit, values])
  have getRaw := listCodeGetCost_le_linear 2 values
  have getTwo : getCost 2 values ≤ 30000 * unit := by
    exact getRaw.trans (by
      simp [unit, flatPackedCenterContextUnit, values])
  have zeroEstimate := listCodePrependCost_le_of values [0] values
    (zeroCost values) (idCost values) (2 * unit) valuesSpace zeroSpace
    zeroAndContextSpace
  have zeroAndContextBound : zeroAndContext ≤ 10020 * unit := by
    simp only [zeroAndContext]
    omega
  have validEstimate := listCodePrependCost_le_of values [1] (0 :: values)
    (oneCost values) zeroAndContext (2 * unit) valuesSpace oneSpace
    validIndexAndContextSpace
  have validIndexAndContextBound : validIndexAndContext ≤ 30030 * unit := by
    simp only [validIndexAndContext]
    omega
  have finalEstimate := listCodePrependCost_le_of values
    [periodicStrip.motif.length] (1 :: 0 :: values)
    (getCost 2 values) validIndexAndContext (2 * unit) valuesSpace motifSpace
    finalSpace
  change prependCost values [periodicStrip.motif.length] (1 :: 0 :: values)
      (getCost 2 values) validIndexAndContext ≤ 100000 * unit
  omega

def flatPackedCenterValidCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.isCenterValidBool tromino periodicStrip)
    periodicStrip.motif.length
  getCost 0 output +
    (flatPackedCenterFlatCost tromino periodicStrip current next true []
        periodicStrip.motif +
      flatPackedCenterLoopInputCost periodicStrip current next)

theorem flatPackedCenterValid
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedCenterValidCode tromino)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.isCenterValidBool tromino periodicStrip).toNat]
      (flatPackedCenterValidCost tromino periodicStrip current next) := by
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.isCenterValidBool tromino periodicStrip)
    periodicStrip.motif.length
  have loopRaw := flatPackedCenterFlat tromino periodicStrip wellFormed current
    next true [] periodicStrip.motif (by simp)
  have loop : EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedCenterStepCode tromino))
      (periodicStrip.motif.length ::
        Code.flatPackedTransitionScanState periodicStrip current next true 0)
      output
      (flatPackedCenterFlatCost tromino periodicStrip current next true []
        periodicStrip.motif) := by
    simpa [output, flatPackedCenterBaseBool,
      Code.packedCenterBaseValid_all_eq] using loopRaw
  have fitted := comp (get 0 output)
    (comp loop (flatPackedCenterLoopInput periodicStrip current next))
  simpa [Code.flatPackedCenterValidCode,
    flatPackedCenterValidCost, output, flatPackedCenterBaseBool,
    Code.flatPackedTransitionScanState,
    Code.packedCenterBaseValid_all_eq] using fitted

def flatPackedCenterValidSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let unit := flatPackedCenterContextUnit periodicStrip current next
  200000 *
    (flatPackedCenterBodySpaceBound periodicStrip current next * unit +
      unit + 1)

theorem flatPackedCenterValidCost_le_bound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    flatPackedCenterValidCost tromino periodicStrip current next ≤
      flatPackedCenterValidSpaceBound periodicStrip current next := by
  let unit := flatPackedCenterContextUnit periodicStrip current next
  let body := flatPackedCenterBodySpaceBound periodicStrip current next
  let scanCost := flatPackedCenterFlatCost tromino periodicStrip current
    next true [] periodicStrip.motif
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.isCenterValidBool tromino periodicStrip)
    periodicStrip.motif.length
  have additive := flatPackedCenterFlatCost_le_body_mul tromino
    periodicStrip current next true [] periodicStrip.motif (by simp)
  have length := flatPackedCenterMotifLength_le_contextUnit
    periodicStrip current next
  have scanBound : scanCost ≤ body * unit := by
    simp only [scanCost, body, unit]
    calc
      flatPackedCenterFlatCost tromino periodicStrip current next true []
          periodicStrip.motif ≤
        flatPackedCenterBodySpaceBound periodicStrip current next *
          (periodicStrip.motif.length + 1) := additive
      _ ≤ _ := by gcongr
  have scanFit := flatPackedCenterFlat tromino periodicStrip wellFormed current
    next true [] periodicStrip.motif (by simp)
  have outputSpace : encodedListSpace output ≤ scanCost := by
    simpa [output, scanCost, flatPackedCenterBaseBool,
      Code.packedCenterBaseValid_all_eq] using scanFit.output_space
  have projectionRaw := listCodeGetCost_le_linear 0 output
  have projection : getCost 0 output ≤ 10000 * (scanCost + 1) :=
    projectionRaw.trans (by gcongr)
  have input := flatPackedCenterLoopInputCost_le_linear periodicStrip
    current next
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedCenterContextUnit]
  change getCost 0 output +
      (scanCost + flatPackedCenterLoopInputCost periodicStrip current
        next) ≤ 200000 * (body * unit + unit + 1)
  omega

theorem flatPackedCenterValidBounded
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedCenterValidCode tromino)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.isCenterValidBool tromino periodicStrip).toNat]
      (flatPackedCenterValidSpaceBound periodicStrip current next) :=
  (flatPackedCenterValid tromino periodicStrip wellFormed current next).mono
    (flatPackedCenterValidCost_le_bound tromino periodicStrip wellFormed
      current next)

end EvaluatorCodeFits
end PartrecToTM2
end Turing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecFlatPackedOverlapAtSpace
import LeanTrominoes.PartrecFlatPackedOverlapLoop
import LeanTrominoes.PartrecFlatPackedNormalizationAtSpace

/-!
# Evaluator-space certificate for motif-wide flat overlap validity

The exact one-base overlap predicate is lifted through the explicit motif-length
countdown.  Each reachable scan state retains the original flat coordinate
stream, so one native polynomial envelope applies at every step.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedOverlapBaseBool
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (cell : Cell) : Bool :=
  current.overlapsAtBool periodicStrip next column cell

def flatPackedOverlapBaseArgumentsCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let coordinates := values.drop 9
  let restNextWord := prependCost values [next.assignmentWord] coordinates
    (getCost 7 values) (dropCost 9 values)
  let restCurrentWord := prependCost values [current.assignmentWord]
    (next.assignmentWord :: coordinates) (getCost 5 values) restNextWord
  let restY := prependCost values [Encodable.encode cell.2]
    (current.assignmentWord :: next.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
      valid processed.length) restCurrentWord
  let restX := prependCost values [Encodable.encode cell.1]
    (Encodable.encode cell.2 :: current.assignmentWord ::
      next.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
      valid processed.length) restY
  let restNextColumn := prependCost values [column.castSucc.val]
    (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: next.assignmentWord :: coordinates)
    (numeralCost column.castSucc.val values) restX
  let restCurrentColumn := prependCost values [column.succ.val]
    (column.castSucc.val :: Encodable.encode cell.1 ::
      Encodable.encode cell.2 :: current.assignmentWord ::
      next.assignmentWord :: coordinates)
    (numeralCost column.succ.val values) restNextColumn
  prependCost values [periodicStrip.motif.length]
    (column.succ.val :: column.castSucc.val :: Encodable.encode cell.1 ::
      Encodable.encode cell.2 :: current.assignmentWord ::
      next.assignmentWord :: coordinates)
    (getCost 4 values) restCurrentColumn

theorem flatPackedOverlapBaseArguments
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedOverlapAtArgumentsCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      (Code.flatPackedOverlapAtInput periodicStrip.motif column.succ.val
        column.castSucc.val cell current.assignmentWord next.assignmentWord)
      (flatPackedOverlapBaseArgumentsCost column periodicStrip current next valid
        processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have restNextWord := prepend (get 7 values) (drop 9 values)
  have restCurrentWord := prepend (get 5 values) restNextWord
  have restY := prepend
    (flatPackedTransitionCellField (1 : Fin 2) periodicStrip current next valid
      processed cell remaining split) restCurrentWord
  have restX := prepend
    (flatPackedTransitionCellField (0 : Fin 2) periodicStrip current next valid
      processed cell remaining split) restY
  have restNextColumn := prepend (numeral column.castSucc.val values) restX
  have restCurrentColumn := prepend (numeral column.succ.val values)
    restNextColumn
  have result := prepend (get 4 values) restCurrentColumn
  simpa [Code.flatPackedOverlapAtArgumentsCode,
    flatPackedOverlapBaseArgumentsCost,
    Code.flatPackedOverlapAtInput,
    Code.flatPackedTransitionScanState,
    PeriodicStripFlatEncoding.cellFields, prependCost, values] using result

def flatPackedOverlapBaseAtCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  flatPackedOverlapAtCost periodicStrip.motif column.succ.val
      column.castSucc.val cell current.assignmentWord next.assignmentWord +
    flatPackedOverlapBaseArgumentsCost column periodicStrip current next valid
      processed cell

theorem flatPackedOverlapBaseAt
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedOverlapAtIndexedCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(flatPackedOverlapBaseBool column periodicStrip current next cell).toNat]
      (flatPackedOverlapBaseAtCost column periodicStrip current next valid
        processed cell) := by
  have fitted := comp
    (flatPackedOverlapAt periodicStrip.motif column.succ.val
      column.castSucc.val cell current.assignmentWord next.assignmentWord)
    (flatPackedOverlapBaseArguments column periodicStrip current next valid
      processed cell remaining split)
  rw [Code.packedOverlapAtResult_eq_semantic periodicStrip current next
    column cell] at fitted
  simpa [Code.flatPackedOverlapAtIndexedCode, flatPackedOverlapBaseAtCost,
    flatPackedOverlapBaseBool] using fitted

def flatPackedOverlapUpdatedValidCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  boolAndCost values valid.toNat
    (flatPackedOverlapBaseBool column periodicStrip current next cell).toNat
    (getCost 0 values)
    (flatPackedOverlapBaseAtCost column periodicStrip current next valid
      processed cell)

theorem flatPackedOverlapUpdatedValid
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedOverlapUpdatedValidCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(valid && flatPackedOverlapBaseBool column periodicStrip current next cell).toNat]
      (flatPackedOverlapUpdatedValidCost column periodicStrip current
        next valid processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have combined := boolAnd (get 0 values)
    (flatPackedOverlapBaseAt column periodicStrip current next valid
      processed cell remaining split)
  cases valid <;>
    cases normalized :
      flatPackedOverlapBaseBool column periodicStrip current next cell <;>
    simpa [Code.flatPackedOverlapUpdatedValidCode,
      flatPackedOverlapUpdatedValidCost, values,
      Code.flatPackedTransitionScanState, normalized] using combined

def flatPackedOverlapIndexCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  succCost [processed.length] + getCost 1 values

theorem flatPackedOverlapIndex
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) :
    EvaluatorCodeFits (Code.succ.comp (Code.get 1))
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [processed.length + 1]
      (flatPackedOverlapIndexCost periodicStrip current next valid
        processed) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [flatPackedOverlapIndexCost, values,
    Code.flatPackedTransitionScanState, Nat.add_comm] using
    comp (succ_named [processed.length]) (get 1 values)

def flatPackedOverlapIndexAndRestCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  prependCost values [processed.length + 1] (values.drop 2)
    (flatPackedOverlapIndexCost periodicStrip current next valid
      processed) (dropCost 2 values)

theorem flatPackedOverlapIndexAndRest
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    EvaluatorCodeFits
      (Code.prepend (Code.succ.comp (Code.get 1)) (Code.drop 2)) values
      ((processed.length + 1) :: values.drop 2)
      (flatPackedOverlapIndexAndRestCost periodicStrip current next valid
        processed) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [flatPackedOverlapIndexAndRestCost, values, prependCost] using
    prepend (flatPackedOverlapIndex periodicStrip current next valid
      processed) (drop 2 values)

def flatPackedOverlapStepCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let rest := (processed.length + 1) :: values.drop 2
  prependCost values
    [(valid && flatPackedOverlapBaseBool column periodicStrip current next cell).toNat]
    rest
    (flatPackedOverlapUpdatedValidCost column periodicStrip current next
      valid processed cell)
    (flatPackedOverlapIndexAndRestCost periodicStrip current next valid
      processed)

theorem flatPackedOverlapStep
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedOverlapStepCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && flatPackedOverlapBaseBool column periodicStrip current next cell)
        (processed.length + 1))
      (flatPackedOverlapStepCost column periodicStrip current next valid
        processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have fitted := prepend
    (flatPackedOverlapUpdatedValid column periodicStrip current next
      valid processed cell remaining split)
    (flatPackedOverlapIndexAndRest periodicStrip current next valid
      processed)
  simpa [Code.flatPackedOverlapStepCode,
    flatPackedOverlapStepCost, values,
    Code.flatPackedTransitionScanState, prependCost] using fitted

def flatPackedOverlapBodySuccCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remainingCount : Nat) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  flatCountdownBodyCost (fun _ =>
      Code.flatPackedTransitionScanState periodicStrip current next
        (valid && flatPackedOverlapBaseBool column periodicStrip current next cell)
        (processed.length + 1))
    (fun _ => flatPackedOverlapStepCost column periodicStrip current next
      valid processed cell)
    (remainingCount + 1) values

theorem flatPackedOverlapBodySucc
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    let output := Code.flatPackedTransitionScanState periodicStrip current next
      (valid && flatPackedOverlapBaseBool column periodicStrip current next cell)
      (processed.length + 1)
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.flatPackedOverlapStepCode column))
      ((remaining.length + 1) :: values)
      (flatCountdownOutput (fun _ => output) (remaining.length + 1) values)
      (flatPackedOverlapBodySuccCost column periodicStrip current next
        valid processed cell remaining.length) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (valid && flatPackedOverlapBaseBool column periodicStrip current next cell)
    (processed.length + 1)
  have transformed := comp
    (flatPackedOverlapStep column periodicStrip current next valid
      processed cell remaining split)
    (tail_named (remaining.length :: values))
  have payloadResult := prepend (head (remaining.length :: values)) transformed
  have branch := prepend (one (remaining.length :: values)) payloadResult
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedOverlapBodySuccCost, flatCountdownBodyCost,
    flatCountdownSuccBranchCost, values, output, prependCost, Code.prepend] using
    EvaluatorCodeFits.case_succ
      (zeroBranch := Code.zero')
      (values := (remaining.length + 1) :: values)
      (predecessor := remaining.length) (by rfl) branch

def flatPackedOverlapBodyZeroCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  flatCountdownBodyCost (fun _ => values) (fun _ => 0) 0 values

theorem flatPackedOverlapBodyZero
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.flatPackedOverlapStepCode column))
      (0 :: values) (flatCountdownOutput (fun _ => values) 0 values)
      (flatPackedOverlapBodyZeroCost periodicStrip current next valid
        processed) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedOverlapBodyZeroCost, flatCountdownBodyCost, values,
    zeroPrimeCost] using
    EvaluatorCodeFits.case_zero
      (successorBranch :=
        .cons Code.one
          (.cons Code.head
            ((Code.flatPackedOverlapStepCode column).comp Code.tail)))
      (values := 0 :: values) (by rfl) (zero'_named values)

def flatPackedOverlapFlatCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    Bool → List Cell → List Cell → Nat
  | valid, processed, [] =>
      flatPackedOverlapBodyZeroCost periodicStrip current next valid
        processed
  | valid, processed, cell :: remaining =>
      let nextValid :=
        valid && flatPackedOverlapBaseBool column periodicStrip current next cell
      flatPackedOverlapBodySuccCost column periodicStrip current next
          valid processed cell remaining.length +
        flatPackedOverlapFlatCost column periodicStrip current next
          nextValid (processed ++ [cell]) remaining

theorem flatPackedOverlapResultSpace_le_cost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    encodedListSpace
        (Code.flatPackedTransitionScanState periodicStrip current next
          (valid && remaining.all fun cell =>
            flatPackedOverlapBaseBool column periodicStrip current next cell)
          periodicStrip.motif.length) ≤
      flatPackedOverlapFlatCost column periodicStrip current next valid
        processed remaining := by
  induction remaining generalizing valid processed with
  | nil =>
      have motifEq : periodicStrip.motif = processed := by simpa using split
      have output := (flatPackedOverlapBodyZero column periodicStrip
        current next valid processed).output_space
      simpa [flatCountdownOutput, flatPackedOverlapFlatCost, motifEq,
        Code.flatPackedTransitionScanState] using
        (listCodeEncodedListSpace_tail_le
          (0 :: Code.flatPackedTransitionScanState periodicStrip current next
            valid processed.length)).trans output
  | cons cell remaining induction =>
      let nextValid :=
        valid && flatPackedOverlapBaseBool column periodicStrip current next cell
      let nextProcessed := processed ++ [cell]
      have nextSplit : periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have tail := induction nextValid nextProcessed nextSplit
      simpa [flatPackedOverlapFlatCost, nextValid, nextProcessed,
        Bool.and_assoc] using tail.trans (Nat.le_add_left _ _)

theorem flatPackedOverlapFlat
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedOverlapStepCode column))
      (remaining.length ::
        Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && remaining.all fun cell =>
          flatPackedOverlapBaseBool column periodicStrip current next cell)
        periodicStrip.motif.length)
      (flatPackedOverlapFlatCost column periodicStrip current next valid
        processed remaining) where
  input_space := by
    cases remaining with
    | nil =>
        exact (flatPackedOverlapBodyZero column periodicStrip current next
          valid processed).input_space
    | cons cell remaining =>
        have headSplit : periodicStrip.motif =
            processed ++ cell :: remaining := split
        exact (flatPackedOverlapBodySucc column periodicStrip           current next valid processed cell remaining headSplit).input_space.trans (by
            simp [flatPackedOverlapFlatCost])
  output_space := flatPackedOverlapResultSpace_le_cost column
    periodicStrip current next valid processed remaining split
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction remaining generalizing valid processed with
    | nil =>
        let values := Code.flatPackedTransitionScanState periodicStrip current
          next valid processed.length
        have motifEq : periodicStrip.motif = processed := by simpa using split
        have body := flatPackedOverlapBodyZero column periodicStrip
          current next valid processed
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    (Code.flatPackedOverlapStepCode column))
                  continuation)
                (flatCountdownOutput (fun _ => values) 0 values)) := by
          apply EvaluatorExecutionFits.ret_fix_zero
          · rfl
          · simp only [continuationSpace_fix]
            have output := body.output_space
            simp only [flatPackedOverlapFlatCost] at budget
            simp only [values] at *
            omega
          · simpa [flatCountdownOutput, values, motifEq,
              Code.flatPackedTransitionScanState] using after
        exact body.call
          (.fix
            (Code.flatCountdownBody
              (Code.flatPackedOverlapStepCode column))
            continuation)
          bound
          (by
            simp only [continuationSpace_fix,
              flatPackedOverlapFlatCost] at *
            exact budget)
          fixedAfter
    | cons cell remaining induction =>
        let nextValid :=
          valid && flatPackedOverlapBaseBool column periodicStrip current next cell
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
        have body := flatPackedOverlapBodySucc column periodicStrip           current next valid processed cell remaining headSplit
        have recursiveBudget :
            flatPackedOverlapFlatCost column periodicStrip current next
                nextValid nextProcessed remaining +
              continuationSpace continuation ≤ bound := by
          have raw : flatPackedOverlapFlatCost column periodicStrip
                current next
                (valid && flatPackedOverlapBaseBool column periodicStrip current next cell)
                (processed ++ [cell]) remaining +
              continuationSpace continuation ≤ bound := by
            simp only [flatPackedOverlapFlatCost] at budget
            omega
          simpa only [nextValid, nextProcessed] using raw
        have recursiveAfter :
            EvaluatorExecutionFits bound
              (.ret continuation
                (Code.flatPackedTransitionScanState periodicStrip current next
                  (nextValid && remaining.all fun tailCell =>
                    flatPackedOverlapBaseBool column periodicStrip current next
                      tailCell)
                  periodicStrip.motif.length)) := by
          simpa [nextValid, Bool.and_assoc] using after
        have recursiveBody := induction nextValid nextProcessed nextSplit
          recursiveBudget recursiveAfter
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    (Code.flatPackedOverlapStepCode column))
                  continuation)
                (flatCountdownOutput (fun _ => output)
                  (remaining.length + 1) values)) := by
          apply EvaluatorExecutionFits.ret_fix_succ
          · simp [flatCountdownOutput, output, nextValid]
          · simp only [continuationSpace_fix]
            have outputSpace := body.output_space
            simp only [flatPackedOverlapFlatCost] at budget
            simp only [values, output, nextValid, nextProcessed] at *
            omega
          · simpa [flatCountdownOutput, output, nextValid,
              nextProcessed] using recursiveBody
        exact body.call
          (.fix
            (Code.flatCountdownBody
              (Code.flatPackedOverlapStepCode column))
            continuation)
          bound
          (by
            simp only [continuationSpace_fix]
            simp only [flatPackedOverlapFlatCost] at budget
            omega)
          fixedAfter

/-! ## Native polynomial bounds -/

def flatPackedOverlapContextUnit
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next) + 10

def flatPackedOverlapAtUnit (values : List Nat) : Nat :=
  encodedListSpace values + 10

def flatPackedOverlapContextCore
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  (10 ^ 1000) *
    (flatPackedOverlapContextUnit periodicStrip current next) ^ 2

def flatPackedOverlapBodySpaceBound
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  (10 ^ 1100) *
    (flatPackedOverlapContextUnit periodicStrip current next) ^ 2

theorem flatPackedOverlapContextCore_large
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) :
    1000000 * flatPackedOverlapContextUnit periodicStrip current next +
        1000 ≤
      flatPackedOverlapContextCore periodicStrip current next := by
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  have positive : 10 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
  have squareDominates : unit ≤ unit ^ 2 := by nlinarith
  simp only [flatPackedOverlapContextCore]
  change 1000000 * unit + 1000 ≤ _ * unit ^ 2
  omega

theorem flatPackedOverlapScanUnit_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (index : Nat) (indexBound : index ≤ periodicStrip.motif.length) :
    flatPackedOverlapAtUnit
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          index) ≤
      2 * flatPackedOverlapContextUnit periodicStrip current next := by
  let context := Code.flatPackedTransitionContext periodicStrip current next
  have indexBits := listCodeEncodeNat_length_mono indexBound
  have motifMember : periodicStrip.motif.length ∈ context := by
    simp [context, Code.flatPackedTransitionContext]
  have motifSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length context motifMember
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases valid <;>
    simp [flatPackedOverlapAtUnit,
      flatPackedOverlapContextUnit,
      Code.flatPackedTransitionScanState,
      Code.flatPackedTransitionContext, context,
      encodedListSpace_cons, zeroBits, oneBits] at * <;>
    omega

theorem flatPackedOverlapAtInputUnit_le_context
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapAtInputUnit periodicStrip.motif column.succ.val
        column.castSucc.val cell current.assignmentWord next.assignmentWord ≤
      16 * flatPackedOverlapContextUnit periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip current
    next valid processed.length indexBound
  have valuesBound : encodedListSpace values + 10 ≤ 2 * unit := by
    simpa [values, unit, flatPackedOverlapAtUnit] using scanUnit
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  have coordinates := flatPackedTransitionCoordinatesSpace_le periodicStrip
    current next valid processed.length
  have lengthMember : periodicStrip.motif.length ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have currentWordMember : current.assignmentWord ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have nextWordMember : next.assignmentWord ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have lengthSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length values lengthMember
  have currentWordSpace := flatPackedTransitionScanMemberSpace_le
    current.assignmentWord values currentWordMember
  have nextWordSpace := flatPackedTransitionScanMemberSpace_le
    next.assignmentWord values nextWordMember
  have currentColumnBound : column.succ.val ≤ 4 := by omega
  have nextColumnBound : column.castSucc.val ≤ 4 := by omega
  have currentColumnBits := listCodeEncodeNat_length_mono currentColumnBound
  have nextColumnBits := listCodeEncodeNat_length_mono nextColumnBound
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  rw [fourBits] at currentColumnBits nextColumnBits
  change encodedListSpace
      (Code.flatPackedOverlapAtInput periodicStrip.motif column.succ.val
        column.castSucc.val cell current.assignmentWord next.assignmentWord) +
      10 ≤
    16 * unit
  simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace coordinates lengthSpace currentWordSpace nextWordSpace
  simp only [Code.flatPackedOverlapAtInput, List.cons_append,
    List.nil_append, encodedListSpace_cons]
  simp only [values] at xSpace ySpace coordinates lengthSpace currentWordSpace nextWordSpace valuesBound
  omega

theorem flatPackedOverlapBaseArgumentsCost_le_quadratic
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapBaseArgumentsCost column periodicStrip current next valid
        processed cell ≤
      (10 ^ 100) *
        (flatPackedOverlapContextUnit periodicStrip current next) ^ 2 := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip current
    next valid processed.length indexBound
  have scanSpace : encodedListSpace values + 1 ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have getBound : ∀ index : Nat, index ≤ 9 →
      getCost index values ≤ 200000 * unit := by
    intro index fixed
    have raw := listCodeGetCost_le_linear index values
    calc
      _ ≤ (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
      _ ≤ 100000 * (2 * unit) := by gcongr; omega
      _ = 200000 * unit := by ring
  have get4 := getBound 4 (by omega)
  have get5 := getBound 5 (by omega)
  have get7 := getBound 7 (by omega)
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
      simpa [flatPackedNormalizationAtUnit, flatPackedOverlapAtUnit,
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
  have zeroRaw := listCodeZeroCost_le_linear values
  have zeroBound : zeroCost values ≤ 20000 * unit := by
    calc
      zeroCost values ≤ 10000 * (encodedListSpace values + 1) := zeroRaw
      _ ≤ 10000 * (2 * unit) := by gcongr
      _ = 20000 * unit := by ring
  have currentAdd : addConstCost column.succ.val [0] ≤ 1000000 := by
    fin_cases column <;> native_decide
  have nextAdd : addConstCost column.castSucc.val [0] ≤ 1000000 := by
    fin_cases column <;> native_decide
  have currentNumeral : numeralCost column.succ.val values ≤
      2000000 * unit := by
    simp only [numeralCost]
    omega
  have nextNumeral : numeralCost column.castSucc.val values ≤
      2000000 * unit := by
    simp only [numeralCost]
    omega
  have currentNumeral' : numeralCost (column.val + 1) values ≤
      2000000 * unit := by simpa using currentNumeral
  have nextNumeral' : numeralCost column.val values ≤
      2000000 * unit := by simpa using nextNumeral
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  have coordinatesSpace : encodedListSpace (values.drop 9) ≤
      encodedListSpace values := dynamicDropSpace_drop_le 9 values
  have lengthMember : periodicStrip.motif.length ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have currentWordMember : current.assignmentWord ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have nextWordMember : next.assignmentWord ∈ values := by
    simp [values, Code.flatPackedTransitionScanState]
  have lengthSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length values lengthMember
  have currentWordSpace := flatPackedTransitionScanMemberSpace_le
    current.assignmentWord values currentWordMember
  have nextWordSpace := flatPackedTransitionScanMemberSpace_le
    next.assignmentWord values nextWordMember
  have currentColumnBound : column.succ.val ≤ 4 := by omega
  have nextColumnBound : column.castSucc.val ≤ 4 := by omega
  have currentColumnBits := listCodeEncodeNat_length_mono currentColumnBound
  have nextColumnBits := listCodeEncodeNat_length_mono nextColumnBound
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  rw [fourBits] at currentColumnBits nextColumnBits
  have currentColumnBits' :
      (Computability.encodeNat (column.val + 1)).length ≤ 3 := by
    simpa using currentColumnBits
  have nextColumnBits' :
      (Computability.encodeNat column.val).length ≤ 3 := by
    simpa using nextColumnBits
  change flatPackedOverlapBaseArgumentsCost column periodicStrip current next valid
      processed cell ≤ (10 ^ 100) * unit ^ 2
  simp [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace lengthSpace currentWordSpace nextWordSpace
  simp [flatPackedOverlapBaseArgumentsCost, prependCost,
    encodedListSpace_cons, encodedListSpace_nil]
  simp only [values] at *
  omega

theorem flatPackedOverlapBaseAtCost_le_context_core
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapBaseAtCost column periodicStrip current next valid
        processed cell ≤
      flatPackedOverlapContextCore periodicStrip current next := by
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  have inputUnit := flatPackedOverlapAtInputUnit_le_context column
    periodicStrip current next valid processed cell remaining split
  have baseCost : flatPackedOverlapAtCost periodicStrip.motif column.succ.val
      column.castSucc.val cell current.assignmentWord next.assignmentWord ≤
      256 * (10 ^ 90) * unit ^ 2 := by
    calc
      _ ≤ flatPackedOverlapAtSpaceBound periodicStrip.motif column.succ.val
          column.castSucc.val cell current.assignmentWord next.assignmentWord :=
        flatPackedOverlapAtCost_le_quadratic periodicStrip.motif
          column.succ.val column.castSucc.val cell current.assignmentWord
            next.assignmentWord
      _ = (10 ^ 90) *
          (flatPackedOverlapAtInputUnit periodicStrip.motif column.succ.val
            column.castSucc.val cell current.assignmentWord
              next.assignmentWord) ^ 2 := rfl
      _ ≤ (10 ^ 90) * (16 * unit) ^ 2 := by gcongr
      _ = 256 * (10 ^ 90) * unit ^ 2 := by ring
  have arguments := flatPackedOverlapBaseArgumentsCost_le_quadratic
    column periodicStrip current next valid processed cell remaining split
  have coefficientBound :
      256 * (10 ^ 90) + 10 ^ 100 ≤ 10 ^ 1000 := by native_decide
  change flatPackedOverlapAtCost periodicStrip.motif column.succ.val
        column.castSucc.val cell current.assignmentWord next.assignmentWord +
      flatPackedOverlapBaseArgumentsCost column periodicStrip current next valid
        processed cell ≤
    flatPackedOverlapContextCore periodicStrip current next
  calc
    _ ≤ 256 * (10 ^ 90) * unit ^ 2 + (10 ^ 100) * unit ^ 2 :=
      Nat.add_le_add baseCost arguments
    _ = (256 * (10 ^ 90) + 10 ^ 100) * unit ^ 2 := by ring
    _ ≤ (10 ^ 1000) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficientBound
    _ = flatPackedOverlapContextCore periodicStrip current next := by
      rfl

theorem flatPackedOverlapGetCost_le_context_core
    (index : Nat) (fixed : index ≤ 9)
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    getCost index
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedOverlapContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid scanIndex
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid scanIndex indexBound
  have scanSpace : encodedListSpace values + 1 ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have raw := listCodeGetCost_le_linear index values
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
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
    _ = flatPackedOverlapContextCore periodicStrip current next := by
      rfl

theorem flatPackedOverlapDropTwoCost_le_context_core
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    dropCost 2
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedOverlapContextCore periodicStrip current next := by
  have whole := flatPackedOverlapGetCost_le_context_core 2 (by omega)
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

theorem flatPackedOverlapDropNineCost_le_context_core
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    dropCost 9
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedOverlapContextCore periodicStrip current next := by
  have whole := flatPackedOverlapGetCost_le_context_core 9 (by omega)
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
theorem flatPackedOverlapUpdatedValidCost_le_context
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapUpdatedValidCost column periodicStrip current next
        valid processed cell ≤
      2000 * flatPackedOverlapContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let core := flatPackedOverlapContextCore periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid processed.length indexBound
  have scanSpace : encodedListSpace values + 10 ≤ 2 * unit := by
    simpa [values, unit, flatPackedOverlapAtUnit] using scanUnit
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
  have squareDominates : unit ≤ unit ^ 2 := by nlinarith
  have coreLarge : 2 * unit + 1 ≤ core := by
    simp only [core, flatPackedOverlapContextCore]
    change 2 * unit + 1 ≤ _ * unit ^ 2
    omega
  have valuesBound : encodedListSpace values ≤ core := by
    omega
  have get0 := flatPackedOverlapGetCost_le_context_core 0 (by omega)
    periodicStrip current next valid processed.length indexBound
  have atCost := flatPackedOverlapBaseAtCost_le_context_core column
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
    (flatPackedOverlapBaseBool column periodicStrip current next cell).toNat
    (getCost 0 values)
    (flatPackedOverlapBaseAtCost column periodicStrip current next valid
      processed cell)
    core (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
      headSuccessorBound (by simpa [values, core] using get0)
      (by simpa [core] using atCost) positive
  have exact : flatPackedOverlapUpdatedValidCost column periodicStrip
      current next valid processed cell ≤ 1000 * (core + 1) := by
    simpa [flatPackedOverlapUpdatedValidCost, values] using wrapped
  exact exact.trans (by
    omega)

theorem flatPackedOverlapIndexCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell)
    (processedBound : processed.length ≤ periodicStrip.motif.length) :
    flatPackedOverlapIndexCost periodicStrip current next valid
        processed ≤
      2 * flatPackedOverlapContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let core := flatPackedOverlapContextCore periodicStrip current next
  have get1 := flatPackedOverlapGetCost_le_context_core 1 (by omega)
    periodicStrip current next valid processed.length processedBound
  have selected := flatMotifIndexSelectedSpace_le 1 values
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have selectedSpace : encodedListSpace [processed.length] ≤ 2 * unit := by
    have valueEq : values[1]?.getD 0 = processed.length := by
      simp [values, Code.flatPackedTransitionScanState]
    rw [valueEq] at selected
    simp only [flatPackedOverlapAtUnit] at scanUnit
    exact selected.trans (by
      simp only [values, unit]
      omega)
  have successorRaw := succCost_le [processed.length]
  have coreLarge := flatPackedOverlapContextCore_large periodicStrip
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

theorem flatPackedOverlapIndexAndRestCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) (cell : Cell)
    (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapIndexAndRestCost periodicStrip current next valid
        processed ≤
      4 * flatPackedOverlapContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let core := flatPackedOverlapContextCore periodicStrip current next
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have indexCost := flatPackedOverlapIndexCost_le_context periodicStrip
    current next valid processed processedBound
  have dropBound := flatPackedOverlapDropTwoCost_le_context_core
    periodicStrip current next valid processed.length processedBound
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have nextScanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid (processed.length + 1) nextBound
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at scanUnit
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
    simp [unit, flatPackedOverlapContextUnit] at motifSpace ⊢
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
      simp only [flatPackedOverlapAtUnit] at nextScanUnit
      simp only [unit]
      omega)
  have raw := listCodePrependCost_le_of values [processed.length + 1]
    (values.drop 2)
    (flatPackedOverlapIndexCost periodicStrip current next valid
      processed) (EvaluatorCodeFits.dropCost 2 values) (2 * unit) valuesSpace fieldSpace (by
        simpa only [List.headI_cons] using outputSpace)
  have coreLarge := flatPackedOverlapContextCore_large periodicStrip
    current next
  have overhead : 6 * unit + 2 ≤ core := by omega
  change prependCost values [processed.length + 1] (values.drop 2)
    (flatPackedOverlapIndexCost periodicStrip current next valid
      processed) (EvaluatorCodeFits.dropCost 2 values) ≤ 4 * core
  change flatPackedOverlapIndexCost periodicStrip current next valid
    processed ≤ 2 * core at indexCost
  change EvaluatorCodeFits.dropCost 2 values ≤ core at dropBound
  omega

theorem flatPackedOverlapStepCost_le_context
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapStepCost column periodicStrip current next valid
        processed cell ≤
      2005 * flatPackedOverlapContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let core := flatPackedOverlapContextCore periodicStrip current next
  let nextValid := valid && flatPackedOverlapBaseBool column periodicStrip current next cell
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have updated := flatPackedOverlapUpdatedValidCost_le_context column
    periodicStrip current next valid processed cell remaining split
  have rest := flatPackedOverlapIndexAndRestCost_le_context periodicStrip
    current next valid processed cell remaining split
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have nextScanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next nextValid (processed.length + 1) nextBound
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have fieldSpace : encodedListSpace [nextValid.toNat] ≤ 2 * unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases nextValid with
    | false =>
        simp [unit, flatPackedOverlapContextUnit,
          encodedListSpace_cons, zeroBits]
        omega
    | true =>
        simp [unit, flatPackedOverlapContextUnit,
          encodedListSpace_cons, oneBits]
  have outputSpace : encodedListSpace
      (Code.flatPackedTransitionScanState periodicStrip current next nextValid
        (processed.length + 1)) ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at nextScanUnit
    simp only [unit]
    omega
  have raw := listCodePrependCost_le_of values [nextValid.toNat]
    ((processed.length + 1) :: values.drop 2)
    (flatPackedOverlapUpdatedValidCost column periodicStrip current next
      valid processed cell)
    (flatPackedOverlapIndexAndRestCost periodicStrip current next valid
      processed) (2 * unit) valuesSpace fieldSpace (by
        simpa [nextValid, values, Code.flatPackedTransitionScanState] using
          outputSpace)
  have coreLarge := flatPackedOverlapContextCore_large periodicStrip
    current next
  have overhead : 6 * unit + 2 ≤ core := by omega
  change prependCost values [nextValid.toNat]
      ((processed.length + 1) :: values.drop 2)
      (flatPackedOverlapUpdatedValidCost column periodicStrip current next
        valid processed cell)
      (flatPackedOverlapIndexAndRestCost periodicStrip current next valid
        processed) ≤ 2005 * core
  change flatPackedOverlapUpdatedValidCost column periodicStrip current
    next valid processed cell ≤ 2000 * core at updated
  change flatPackedOverlapIndexAndRestCost periodicStrip current next
    valid processed ≤ 4 * core at rest
  omega

theorem flatPackedOverlapBodySuccCost_le_context
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedOverlapBodySuccCost column periodicStrip current next valid
        processed cell remaining.length ≤
      flatPackedOverlapBodySpaceBound periodicStrip current next := by
  let payload := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let nextValid := valid && flatPackedOverlapBaseBool column periodicStrip current next cell
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    nextValid (processed.length + 1)
  let values := remaining.length :: payload
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let core := flatPackedOverlapContextCore periodicStrip current next
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
    simp [unit, flatPackedOverlapContextUnit]
  have payloadUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have outputUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next nextValid (processed.length + 1) nextBound
  have payloadSpace : encodedListSpace payload ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at payloadUnit
    simp only [payload, unit]
    omega
  have outputSpace : encodedListSpace output ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at outputUnit
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
    simp [unit, flatPackedOverlapContextUnit] at motifSpace ⊢
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
  have coreLarge := flatPackedOverlapContextCore_large periodicStrip
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
  have step := flatPackedOverlapStepCost_le_context column periodicStrip
    current next valid processed cell remaining split
  change flatPackedOverlapStepCost column periodicStrip current next valid
    processed cell ≤ 2005 * core at step
  let transformedCost :=
    flatPackedOverlapStepCost column periodicStrip current next valid
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
        flatPackedOverlapContextUnit]
      omega)
    (by simpa only [List.headI_cons] using taggedOutputSpace)
  have branchBound : flatCountdownSuccBranchCost (fun _ => output)
      (fun _ => flatPackedOverlapStepCost column periodicStrip current
        next valid processed cell) remaining.length payload ≤
      2010 * core := by
    change prependCost values [1] (remaining.length :: output)
      (oneCost values) payloadCost ≤ 2010 * core
    omega
  have bodyBound : flatPackedOverlapBodySuccCost column periodicStrip
      current next valid processed cell remaining.length ≤ 2011 * core := by
    simp only [flatPackedOverlapBodySuccCost, flatCountdownBodyCost]
    change flatCountdownSuccBranchCost (fun _ => output)
        (fun _ => flatPackedOverlapStepCost column periodicStrip current
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
    flatPackedOverlapBodySuccCost column periodicStrip current next valid
        processed cell remaining.length ≤ 2011 * core := bodyBound
    _ ≤ flatPackedOverlapBodySpaceBound periodicStrip current next := by
      have coefficient : 2011 * (10 ^ 1000) ≤ 10 ^ 1100 := by
        native_decide
      change 2011 * ((10 ^ 1000) * unit ^ 2) ≤
        (10 ^ 1100) * unit ^ 2
      calc
        _ = (2011 * (10 ^ 1000)) * unit ^ 2 :=
          (Nat.mul_assoc 2011 (10 ^ 1000) (unit ^ 2)).symm
        _ ≤ (10 ^ 1100) * unit ^ 2 :=
          Nat.mul_le_mul_right (unit ^ 2) coefficient

theorem flatPackedOverlapBodyZeroCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell)
    (processedBound : processed.length ≤ periodicStrip.motif.length) :
    flatPackedOverlapBodyZeroCost periodicStrip current next valid
        processed ≤
      flatPackedOverlapBodySpaceBound periodicStrip current next := by
  let payload := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  have scanUnit := flatPackedOverlapScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have payloadSpace : encodedListSpace payload ≤ 2 * unit := by
    simp only [flatPackedOverlapAtUnit] at scanUnit
    simp only [payload, unit]
    omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have coreLarge := flatPackedOverlapContextCore_large periodicStrip
    current next
  have coreToBody : flatPackedOverlapContextCore periodicStrip current
      next ≤ flatPackedOverlapBodySpaceBound periodicStrip current
      next := by
    have coefficient : 10 ^ 1000 ≤ 10 ^ 1100 := by native_decide
    change (10 ^ 1000) * unit ^ 2 ≤ (10 ^ 1100) * unit ^ 2
    exact Nat.mul_le_mul_right (unit ^ 2) coefficient
  change zeroPrimeCost payload + encodedListSpace (0 :: payload) +
      encodedListSpace (0 :: payload) + 1 ≤
    flatPackedOverlapBodySpaceBound periodicStrip current next
  have localBound : zeroPrimeCost payload + encodedListSpace (0 :: payload) +
      encodedListSpace (0 :: payload) + 1 ≤
      flatPackedOverlapContextCore periodicStrip current next := by
    simp [zeroPrimeCost, encodedListSpace_cons, zeroBits]
    omega
  exact localBound.trans coreToBody

theorem flatPackedOverlapFlatCost_le_body_mul
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    flatPackedOverlapFlatCost column periodicStrip current next valid
        processed remaining ≤
      flatPackedOverlapBodySpaceBound periodicStrip current next *
        (remaining.length + 1) := by
  induction remaining generalizing valid processed with
  | nil =>
      have processedBound : processed.length ≤
          periodicStrip.motif.length := by
        have lengths := congrArg List.length split
        simp only [List.append_nil] at lengths
        omega
      simpa [flatPackedOverlapFlatCost] using
        flatPackedOverlapBodyZeroCost_le_context periodicStrip current
          next valid processed processedBound
  | cons cell remaining induction =>
      let nextValid :=
        valid && flatPackedOverlapBaseBool column periodicStrip current next cell
      let nextProcessed := processed ++ [cell]
      have headSplit : periodicStrip.motif =
          processed ++ cell :: remaining := by
        simpa [List.append_assoc] using split
      have nextSplit : periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have body := flatPackedOverlapBodySuccCost_le_context column
        periodicStrip current next valid processed cell remaining headSplit
      have tail := induction nextValid nextProcessed nextSplit
      simp only [flatPackedOverlapFlatCost, List.length_cons]
      simp only [nextValid, nextProcessed] at tail
      nlinarith

theorem flatPackedOverlapMotifLength_le_contextUnit
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) :
    periodicStrip.motif.length + 1 ≤
      flatPackedOverlapContextUnit periodicStrip current next := by
  have lengthBound := list_length_le_encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next)
  have contextLength :
      (Code.flatPackedTransitionContext periodicStrip current next).length =
        7 + 2 * periodicStrip.motif.length := by
    simp [Code.flatPackedTransitionContext,
      PeriodicStripFlatEncoding.cellFields, List.length_flatMap]
    omega
  rw [contextLength] at lengthBound
  simp [flatPackedOverlapContextUnit]
  omega

theorem flatPackedOverlapFlatCost_le_cubic
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapFlatCost column periodicStrip current next true []
        periodicStrip.motif ≤
      (10 ^ 1100) *
        (flatPackedOverlapContextUnit periodicStrip current next) ^ 3 := by
  have additive := flatPackedOverlapFlatCost_le_body_mul column
    periodicStrip current next true [] periodicStrip.motif (by simp)
  have length := flatPackedOverlapMotifLength_le_contextUnit
    periodicStrip current next
  calc
    flatPackedOverlapFlatCost column periodicStrip current next true []
        periodicStrip.motif ≤
      flatPackedOverlapBodySpaceBound periodicStrip current next *
        (periodicStrip.motif.length + 1) := additive
    _ ≤ flatPackedOverlapBodySpaceBound periodicStrip current next *
        flatPackedOverlapContextUnit periodicStrip current next := by
      gcongr
    _ = _ := by
      change (10 ^ 1100) *
          (flatPackedOverlapContextUnit periodicStrip current next) ^ 2 *
            flatPackedOverlapContextUnit periodicStrip current next =
        (10 ^ 1100) *
          (flatPackedOverlapContextUnit periodicStrip current next) ^ 3
      have cube :
          (flatPackedOverlapContextUnit periodicStrip current next) ^ 3 =
            (flatPackedOverlapContextUnit periodicStrip current next) ^ 2 *
              flatPackedOverlapContextUnit periodicStrip current next := by
        exact pow_succ _ 2
      rw [cube]
      rw [Nat.mul_assoc]

theorem flatPackedOverlapFlatBounded
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedOverlapStepCode column))
      (remaining.length ::
        Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && remaining.all fun cell =>
          flatPackedOverlapBaseBool column periodicStrip current next cell)
        periodicStrip.motif.length)
      (flatPackedOverlapBodySpaceBound periodicStrip current next *
        (remaining.length + 1)) :=
  (flatPackedOverlapFlat column periodicStrip current next valid
    processed remaining split).mono
      (flatPackedOverlapFlatCost_le_body_mul column periodicStrip current
        next valid processed remaining split)

/-! ## Complete column wrapper -/

def flatPackedOverlapLoopInputCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let zeroAndContext := prependCost values [0] values
    (zeroCost values) (idCost values)
  let validIndexAndContext := prependCost values [1] (0 :: values)
    (oneCost values) zeroAndContext
  prependCost values [periodicStrip.motif.length] (1 :: 0 :: values)
    (getCost 2 values) validIndexAndContext

theorem flatPackedOverlapLoopInput
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedOverlapLoopInputCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      (periodicStrip.motif.length ::
        Code.flatPackedTransitionScanState periodicStrip current next true 0)
      (flatPackedOverlapLoopInputCost periodicStrip current next) := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  have fitted := prepend (get 2 values)
    (prepend (one values) (prepend (zero values) (id values)))
  simpa [Code.flatPackedOverlapLoopInputCode,
    Code.flatPackedNormalizationLoopInputCode,
    flatPackedOverlapLoopInputCost, values, prependCost,
    Code.flatPackedTransitionContext,
    Code.flatPackedTransitionScanState] using fitted

theorem flatPackedOverlapLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapLoopInputCost periodicStrip current next ≤
      100000 *
        flatPackedOverlapContextUnit periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let zeroAndContext := prependCost values [0] values
    (zeroCost values) (idCost values)
  let validIndexAndContext := prependCost values [1] (0 :: values)
    (oneCost values) zeroAndContext
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp [unit, flatPackedOverlapContextUnit, values]
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
      flatPackedOverlapContextUnit, values]
    omega
  have validIndexAndContextSpace :
      encodedListSpace (1 :: 0 :: values) ≤ 2 * unit := by
    simp [encodedListSpace_cons, zeroBits, oneBits, unit,
      flatPackedOverlapContextUnit, values]
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
      flatPackedOverlapContextUnit, values] at prefixBound fieldInValues ⊢
    omega
  have identityRaw := flatLookupIdCost_le_linear values
  have identity : idCost values ≤ 10 * unit := by
    exact identityRaw.trans (by
      simp [unit, flatPackedOverlapContextUnit, values])
  have zeroRaw := listCodeZeroCost_le_linear values
  have zero : zeroCost values ≤ 10000 * unit := by
    exact zeroRaw.trans (by
      simp [unit, flatPackedOverlapContextUnit, values])
  have oneRaw := flatLookupOneCost_le_linear values
  have one : oneCost values ≤ 20000 * unit := by
    exact oneRaw.trans (by
      simp [unit, flatPackedOverlapContextUnit, values])
  have getRaw := listCodeGetCost_le_linear 2 values
  have getTwo : getCost 2 values ≤ 30000 * unit := by
    exact getRaw.trans (by
      simp [unit, flatPackedOverlapContextUnit, values])
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

def flatPackedOverlapColumnCost
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.overlapsColumnBool periodicStrip next column)
    periodicStrip.motif.length
  getCost 0 output +
    (flatPackedOverlapFlatCost column periodicStrip current next true []
        periodicStrip.motif +
      flatPackedOverlapLoopInputCost periodicStrip current next)

theorem flatPackedOverlapColumn
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedOverlapColumnCode column)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.overlapsColumnBool periodicStrip next column).toNat]
      (flatPackedOverlapColumnCost column periodicStrip current next) := by
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.overlapsColumnBool periodicStrip next column)
    periodicStrip.motif.length
  have loopRaw := flatPackedOverlapFlat column periodicStrip current
    next true [] periodicStrip.motif (by simp)
  have loop : EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedOverlapStepCode column))
      (periodicStrip.motif.length ::
        Code.flatPackedTransitionScanState periodicStrip current next true 0)
      output
      (flatPackedOverlapFlatCost column periodicStrip current next true []
        periodicStrip.motif) := by
    simpa [output, flatPackedOverlapBaseBool,
      PackedWindowState.overlapsColumnBool] using loopRaw
  have fitted := comp (get 0 output)
    (comp loop (flatPackedOverlapLoopInput periodicStrip current next))
  simpa [Code.flatPackedOverlapColumnCode,
    flatPackedOverlapColumnCost, output, flatPackedOverlapBaseBool,
    Code.flatPackedTransitionScanState] using fitted

def flatPackedOverlapColumnSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  200000 *
    (flatPackedOverlapBodySpaceBound periodicStrip current next * unit +
      unit + 1)

theorem flatPackedOverlapColumnCost_le_bound
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapColumnCost column periodicStrip current next ≤
      flatPackedOverlapColumnSpaceBound periodicStrip current next := by
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let body := flatPackedOverlapBodySpaceBound periodicStrip current next
  let scanCost := flatPackedOverlapFlatCost column periodicStrip current
    next true [] periodicStrip.motif
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.overlapsColumnBool periodicStrip next column)
    periodicStrip.motif.length
  have additive := flatPackedOverlapFlatCost_le_body_mul column
    periodicStrip current next true [] periodicStrip.motif (by simp)
  have length := flatPackedOverlapMotifLength_le_contextUnit
    periodicStrip current next
  have scanBound : scanCost ≤ body * unit := by
    simp only [scanCost, body, unit]
    calc
      flatPackedOverlapFlatCost column periodicStrip current next true []
          periodicStrip.motif ≤
        flatPackedOverlapBodySpaceBound periodicStrip current next *
          (periodicStrip.motif.length + 1) := additive
      _ ≤ _ := by gcongr
  have scanFit := flatPackedOverlapFlat column periodicStrip current
    next true [] periodicStrip.motif (by simp)
  have outputSpace : encodedListSpace output ≤ scanCost := by
    simpa [output, scanCost, flatPackedOverlapBaseBool,
      PackedWindowState.overlapsColumnBool] using scanFit.output_space
  have projectionRaw := listCodeGetCost_le_linear 0 output
  have projection : getCost 0 output ≤ 10000 * (scanCost + 1) :=
    projectionRaw.trans (by gcongr)
  have input := flatPackedOverlapLoopInputCost_le_linear periodicStrip
    current next
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
  change getCost 0 output +
      (scanCost + flatPackedOverlapLoopInputCost periodicStrip current
        next) ≤ 200000 * (body * unit + unit + 1)
  omega

theorem flatPackedOverlapColumnBounded
    (column : Fin 4) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedOverlapColumnCode column)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.overlapsColumnBool periodicStrip next column).toNat]
      (flatPackedOverlapColumnSpaceBound periodicStrip current next) :=
  (flatPackedOverlapColumn column periodicStrip current next).mono
    (flatPackedOverlapColumnCost_le_bound column periodicStrip current next)

/-! ## Four shared columns -/

def flatPackedOverlapLastTwoCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  boolAndCost values
    (current.overlapsColumnBool periodicStrip next (2 : Fin 4)).toNat
    (current.overlapsColumnBool periodicStrip next (3 : Fin 4)).toNat
    (flatPackedOverlapColumnCost (2 : Fin 4) periodicStrip current next)
    (flatPackedOverlapColumnCost (3 : Fin 4) periodicStrip current next)

theorem flatPackedOverlapLastTwo
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.flatPackedOverlapColumnCode (2 : Fin 4))
        (Code.flatPackedOverlapColumnCode (3 : Fin 4)))
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool periodicStrip next (3 : Fin 4)).toNat]
      (flatPackedOverlapLastTwoCost periodicStrip current next) := by
  have combined := boolAnd
    (flatPackedOverlapColumn (2 : Fin 4) periodicStrip current next)
    (flatPackedOverlapColumn (3 : Fin 4) periodicStrip current next)
  cases second :
      current.overlapsColumnBool periodicStrip next (2 : Fin 4) <;>
    cases third :
      current.overlapsColumnBool periodicStrip next (3 : Fin 4) <;>
    simpa [flatPackedOverlapLastTwoCost, second, third] using combined

def flatPackedOverlapLastThreeCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let tailTag :=
    (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
      current.overlapsColumnBool periodicStrip next (3 : Fin 4)).toNat
  boolAndCost values
    (current.overlapsColumnBool periodicStrip next (1 : Fin 4)).toNat
    tailTag
    (flatPackedOverlapColumnCost (1 : Fin 4) periodicStrip current next)
    (flatPackedOverlapLastTwoCost periodicStrip current next)

theorem flatPackedOverlapLastThree
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits
      (Code.boolAnd
        (Code.flatPackedOverlapColumnCode (1 : Fin 4))
        (Code.boolAnd
          (Code.flatPackedOverlapColumnCode (2 : Fin 4))
          (Code.flatPackedOverlapColumnCode (3 : Fin 4))))
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
        (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
          current.overlapsColumnBool periodicStrip next (3 : Fin 4))).toNat]
      (flatPackedOverlapLastThreeCost periodicStrip current next) := by
  have combined := boolAnd
    (flatPackedOverlapColumn (1 : Fin 4) periodicStrip current next)
    (flatPackedOverlapLastTwo periodicStrip current next)
  cases first :
      current.overlapsColumnBool periodicStrip next (1 : Fin 4) <;>
    cases second :
      current.overlapsColumnBool periodicStrip next (2 : Fin 4) <;>
    cases third :
      current.overlapsColumnBool periodicStrip next (3 : Fin 4) <;>
    simpa [flatPackedOverlapLastThreeCost, first, second, third] using combined

def flatPackedOverlapColumnsCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let tailTag :=
    (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool periodicStrip next (3 : Fin 4))).toNat
  boolAndCost values
    (current.overlapsColumnBool periodicStrip next (0 : Fin 4)).toNat
    tailTag
    (flatPackedOverlapColumnCost (0 : Fin 4) periodicStrip current next)
    (flatPackedOverlapLastThreeCost periodicStrip current next)

theorem flatPackedOverlapColumns
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedOverlapColumnsCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [((List.finRange 4).all fun column =>
        current.overlapsColumnBool periodicStrip next column).toNat]
      (flatPackedOverlapColumnsCost periodicStrip current next) := by
  have combined := boolAnd
    (flatPackedOverlapColumn (0 : Fin 4) periodicStrip current next)
    (flatPackedOverlapLastThree periodicStrip current next)
  cases zero :
      current.overlapsColumnBool periodicStrip next (0 : Fin 4) <;>
    cases one :
      current.overlapsColumnBool periodicStrip next (1 : Fin 4) <;>
    cases two :
      current.overlapsColumnBool periodicStrip next (2 : Fin 4) <;>
    cases three :
      current.overlapsColumnBool periodicStrip next (3 : Fin 4) <;>
    simpa [Code.flatPackedOverlapColumnsCode, flatPackedOverlapColumnsCost,
      List.finRange_succ, zero, one, two, three] using combined

def flatPackedOverlapColumnsSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let columnBound := flatPackedOverlapColumnSpaceBound periodicStrip current next
  let lastTwoBound := 1000 * (columnBound + 1)
  let lastThreeBound := 1000 * (lastTwoBound + 1)
  1000 * (lastThreeBound + 1)

theorem flatPackedOverlapColumnsCost_le_bound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedOverlapColumnsCost periodicStrip current next ≤
      flatPackedOverlapColumnsSpaceBound periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedOverlapContextUnit periodicStrip current next
  let columnBound := flatPackedOverlapColumnSpaceBound periodicStrip current next
  let lastTwoBound := 1000 * (columnBound + 1)
  let lastThreeBound := 1000 * (lastTwoBound + 1)
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedOverlapContextUnit]
  have contextSpace : encodedListSpace values + 1 ≤ unit := by
    simp [values, unit, flatPackedOverlapContextUnit]
  have unitToColumn : unit ≤ columnBound := by
    simp only [unit, columnBound, flatPackedOverlapColumnSpaceBound]
    omega
  have valuesBound : encodedListSpace values ≤ columnBound := by omega
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBound : (Computability.encodeNat values.headI).length ≤
      columnBound := by
    have localBound : (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans valuesBound
  have successor := listCodeEncodeNat_succ_length_le values.headI
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ columnBound := by
    have localBound :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using successor
    have headPlus : (Computability.encodeNat values.headI).length + 1 ≤
        encodedListSpace values + 1 := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans (headPlus.trans (contextSpace.trans unitToColumn))
  have columnPositive : 1 ≤ columnBound := by omega
  have cost0 := flatPackedOverlapColumnCost_le_bound (0 : Fin 4)
    periodicStrip current next
  have cost1 := flatPackedOverlapColumnCost_le_bound (1 : Fin 4)
    periodicStrip current next
  have cost2 := flatPackedOverlapColumnCost_le_bound (2 : Fin 4)
    periodicStrip current next
  have cost3 := flatPackedOverlapColumnCost_le_bound (3 : Fin 4)
    periodicStrip current next
  have lastTwo : flatPackedOverlapLastTwoCost periodicStrip current next ≤
      lastTwoBound := by
    have bound := boolAndCost_le_budget values
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4)).toNat
      (current.overlapsColumnBool periodicStrip next (3 : Fin 4)).toNat
      (flatPackedOverlapColumnCost (2 : Fin 4) periodicStrip current next)
      (flatPackedOverlapColumnCost (3 : Fin 4) periodicStrip current next)
      columnBound (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
      headSuccessorBound cost2 cost3 columnPositive
    simpa [flatPackedOverlapLastTwoCost, values, lastTwoBound] using bound
  have valuesLastTwo : encodedListSpace values ≤ lastTwoBound :=
    valuesBound.trans (by simp only [lastTwoBound]; omega)
  have headLastTwo : (Computability.encodeNat values.headI).length ≤
      lastTwoBound := headBound.trans (by simp only [lastTwoBound]; omega)
  have headSuccessorLastTwo :
      (Computability.encodeNat (values.headI + 1)).length ≤ lastTwoBound :=
    headSuccessorBound.trans (by simp only [lastTwoBound]; omega)
  have cost1LastTwo :
      flatPackedOverlapColumnCost (1 : Fin 4) periodicStrip current next ≤
        lastTwoBound := cost1.trans (by simp only [lastTwoBound]; omega)
  have lastTwoPositive : 1 ≤ lastTwoBound := by
    simp only [lastTwoBound]
    omega
  have lastThree : flatPackedOverlapLastThreeCost periodicStrip current next ≤
      lastThreeBound := by
    have bound := boolAndCost_le_budget values
      (current.overlapsColumnBool periodicStrip next (1 : Fin 4)).toNat
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool periodicStrip next (3 : Fin 4)).toNat
      (flatPackedOverlapColumnCost (1 : Fin 4) periodicStrip current next)
      (flatPackedOverlapLastTwoCost periodicStrip current next)
      lastTwoBound (Bool.toNat_le _) (Bool.toNat_le _) valuesLastTwo
      headLastTwo headSuccessorLastTwo cost1LastTwo lastTwo lastTwoPositive
    simpa [flatPackedOverlapLastThreeCost, values, lastThreeBound] using bound
  have valuesLastThree : encodedListSpace values ≤ lastThreeBound :=
    valuesLastTwo.trans (by simp only [lastThreeBound]; omega)
  have headLastThree : (Computability.encodeNat values.headI).length ≤
      lastThreeBound := headLastTwo.trans (by simp only [lastThreeBound]; omega)
  have headSuccessorLastThree :
      (Computability.encodeNat (values.headI + 1)).length ≤
        lastThreeBound :=
    headSuccessorLastTwo.trans (by simp only [lastThreeBound]; omega)
  have cost0LastThree :
      flatPackedOverlapColumnCost (0 : Fin 4) periodicStrip current next ≤
        lastThreeBound := cost0.trans (by
          simp only [lastThreeBound, lastTwoBound]
          omega)
  have lastThreePositive : 1 ≤ lastThreeBound := by
    simp only [lastThreeBound]
    omega
  have whole := boolAndCost_le_budget values
    (current.overlapsColumnBool periodicStrip next (0 : Fin 4)).toNat
    (current.overlapsColumnBool periodicStrip next (1 : Fin 4) &&
      (current.overlapsColumnBool periodicStrip next (2 : Fin 4) &&
        current.overlapsColumnBool periodicStrip next (3 : Fin 4))).toNat
    (flatPackedOverlapColumnCost (0 : Fin 4) periodicStrip current next)
    (flatPackedOverlapLastThreeCost periodicStrip current next)
    lastThreeBound (Bool.toNat_le _) (Bool.toNat_le _) valuesLastThree
    headLastThree headSuccessorLastThree cost0LastThree lastThree
    lastThreePositive
  simpa [flatPackedOverlapColumnsCost, flatPackedOverlapColumnsSpaceBound,
    values, columnBound, lastTwoBound, lastThreeBound] using whole

theorem flatPackedOverlapColumnsBounded
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedOverlapColumnsCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      [((List.finRange 4).all fun column =>
        current.overlapsColumnBool periodicStrip next column).toNat]
      (flatPackedOverlapColumnsSpaceBound periodicStrip current next) :=
  (flatPackedOverlapColumns periodicStrip current next).mono
    (flatPackedOverlapColumnsCost_le_bound periodicStrip current next)

end EvaluatorCodeFits
end PartrecToTM2
end Turing

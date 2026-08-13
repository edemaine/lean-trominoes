/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecFlatPackedNormalizationAtSpace
import LeanTrominoes.PartrecFlatPackedNormalizationLoop

/-!
# Evaluator-space certificate for motif-wide flat normalization

The exact indexed normalization predicate is lifted through the explicit
motif-length countdown.  Each reachable scan state retains the original flat
coordinate stream, so one native polynomial envelope applies at every step.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedNormalizationUpdatedValidCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  boolAndCost values valid.toNat
    (current.normalizedAtBool periodicStrip column cell).toNat
    (getCost 0 values)
    (flatPackedNormalizedAtCost column periodicStrip current next valid
      processed cell)

theorem flatPackedNormalizationUpdatedValid
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizationUpdatedValidCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(valid && current.normalizedAtBool periodicStrip column cell).toNat]
      (flatPackedNormalizationUpdatedValidCost column periodicStrip current
        next valid processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have combined := boolAnd (get 0 values)
    (flatPackedNormalizedAt column periodicStrip current next valid processed
      cell remaining split)
  cases valid <;>
    cases normalized :
      current.normalizedAtBool periodicStrip column cell <;>
    simpa [Code.flatPackedNormalizationUpdatedValidCode,
      flatPackedNormalizationUpdatedValidCost, values,
      Code.flatPackedTransitionScanState, normalized] using combined

def flatPackedNormalizationIndexCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  succCost [processed.length] + getCost 1 values

theorem flatPackedNormalizationIndex
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) :
    EvaluatorCodeFits (Code.succ.comp (Code.get 1))
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [processed.length + 1]
      (flatPackedNormalizationIndexCost periodicStrip current next valid
        processed) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [flatPackedNormalizationIndexCost, values,
    Code.flatPackedTransitionScanState, Nat.add_comm] using
    comp (succ_named [processed.length]) (get 1 values)

def flatPackedNormalizationIndexAndRestCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  prependCost values [processed.length + 1] (values.drop 2)
    (flatPackedNormalizationIndexCost periodicStrip current next valid
      processed) (dropCost 2 values)

theorem flatPackedNormalizationIndexAndRest
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    EvaluatorCodeFits
      (Code.prepend (Code.succ.comp (Code.get 1)) (Code.drop 2)) values
      ((processed.length + 1) :: values.drop 2)
      (flatPackedNormalizationIndexAndRestCost periodicStrip current next valid
        processed) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [flatPackedNormalizationIndexAndRestCost, values, prependCost] using
    prepend (flatPackedNormalizationIndex periodicStrip current next valid
      processed) (drop 2 values)

def flatPackedNormalizationStepCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let rest := (processed.length + 1) :: values.drop 2
  prependCost values
    [(valid && current.normalizedAtBool periodicStrip column cell).toNat]
    rest
    (flatPackedNormalizationUpdatedValidCost column periodicStrip current next
      valid processed cell)
    (flatPackedNormalizationIndexAndRestCost periodicStrip current next valid
      processed)

theorem flatPackedNormalizationStep
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizationStepCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && current.normalizedAtBool periodicStrip column cell)
        (processed.length + 1))
      (flatPackedNormalizationStepCost column periodicStrip current next valid
        processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have fitted := prepend
    (flatPackedNormalizationUpdatedValid column periodicStrip current next valid
      processed cell remaining split)
    (flatPackedNormalizationIndexAndRest periodicStrip current next valid
      processed)
  simpa [Code.flatPackedNormalizationStepCode,
    flatPackedNormalizationStepCost, values,
    Code.flatPackedTransitionScanState, prependCost] using fitted

def flatPackedNormalizationBodySuccCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remainingCount : Nat) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  flatCountdownBodyCost (fun _ =>
      Code.flatPackedTransitionScanState periodicStrip current next
        (valid && current.normalizedAtBool periodicStrip column cell)
        (processed.length + 1))
    (fun _ => flatPackedNormalizationStepCost column periodicStrip current next
      valid processed cell)
    (remainingCount + 1) values

theorem flatPackedNormalizationBodySucc
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    let output := Code.flatPackedTransitionScanState periodicStrip current next
      (valid && current.normalizedAtBool periodicStrip column cell)
      (processed.length + 1)
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.flatPackedNormalizationStepCode column))
      ((remaining.length + 1) :: values)
      (flatCountdownOutput (fun _ => output) (remaining.length + 1) values)
      (flatPackedNormalizationBodySuccCost column periodicStrip current next
        valid processed cell remaining.length) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (valid && current.normalizedAtBool periodicStrip column cell)
    (processed.length + 1)
  have transformed := comp
    (flatPackedNormalizationStep column periodicStrip current next valid
      processed cell remaining split)
    (tail_named (remaining.length :: values))
  have payloadResult := prepend (head (remaining.length :: values)) transformed
  have branch := prepend (one (remaining.length :: values)) payloadResult
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedNormalizationBodySuccCost, flatCountdownBodyCost,
    flatCountdownSuccBranchCost, values, output, prependCost, Code.prepend] using
    EvaluatorCodeFits.case_succ
      (zeroBranch := Code.zero')
      (values := (remaining.length + 1) :: values)
      (predecessor := remaining.length) (by rfl) branch

def flatPackedNormalizationBodyZeroCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  flatCountdownBodyCost (fun _ => values) (fun _ => 0) 0 values

theorem flatPackedNormalizationBodyZero
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) :
    let values := Code.flatPackedTransitionScanState periodicStrip current next
      valid processed.length
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.flatPackedNormalizationStepCode column))
      (0 :: values) (flatCountdownOutput (fun _ => values) 0 values)
      (flatPackedNormalizationBodyZeroCost periodicStrip current next valid
        processed) := by
  simp only
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatPackedNormalizationBodyZeroCost, flatCountdownBodyCost, values,
    zeroPrimeCost] using
    EvaluatorCodeFits.case_zero
      (successorBranch :=
        .cons Code.one
          (.cons Code.head
            ((Code.flatPackedNormalizationStepCode column).comp Code.tail)))
      (values := 0 :: values) (by rfl) (zero'_named values)

def flatPackedNormalizationFlatCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    Bool → List Cell → List Cell → Nat
  | valid, processed, [] =>
      flatPackedNormalizationBodyZeroCost periodicStrip current next valid
        processed
  | valid, processed, cell :: remaining =>
      let nextValid :=
        valid && current.normalizedAtBool periodicStrip column cell
      flatPackedNormalizationBodySuccCost column periodicStrip current next
          valid processed cell remaining.length +
        flatPackedNormalizationFlatCost column periodicStrip current next
          nextValid (processed ++ [cell]) remaining

theorem flatPackedNormalizationResultSpace_le_cost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    encodedListSpace
        (Code.flatPackedTransitionScanState periodicStrip current next
          (valid && remaining.all fun cell =>
            current.normalizedAtBool periodicStrip column cell)
          periodicStrip.motif.length) ≤
      flatPackedNormalizationFlatCost column periodicStrip current next valid
        processed remaining := by
  induction remaining generalizing valid processed with
  | nil =>
      have motifEq : periodicStrip.motif = processed := by simpa using split
      have output := (flatPackedNormalizationBodyZero column periodicStrip
        current next valid processed).output_space
      simpa [flatCountdownOutput, flatPackedNormalizationFlatCost, motifEq,
        Code.flatPackedTransitionScanState] using
        (listCodeEncodedListSpace_tail_le
          (0 :: Code.flatPackedTransitionScanState periodicStrip current next
            valid processed.length)).trans output
  | cons cell remaining induction =>
      let nextValid :=
        valid && current.normalizedAtBool periodicStrip column cell
      let nextProcessed := processed ++ [cell]
      have nextSplit : periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have tail := induction nextValid nextProcessed nextSplit
      simpa [flatPackedNormalizationFlatCost, nextValid, nextProcessed,
        Bool.and_assoc] using tail.trans (Nat.le_add_left _ _)

theorem flatPackedNormalizationFlat
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedNormalizationStepCode column))
      (remaining.length ::
        Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && remaining.all fun cell =>
          current.normalizedAtBool periodicStrip column cell)
        periodicStrip.motif.length)
      (flatPackedNormalizationFlatCost column periodicStrip current next valid
        processed remaining) where
  input_space := by
    cases remaining with
    | nil =>
        exact (flatPackedNormalizationBodyZero column periodicStrip current next
          valid processed).input_space
    | cons cell remaining =>
        have headSplit : periodicStrip.motif =
            processed ++ cell :: remaining := split
        exact (flatPackedNormalizationBodySucc column periodicStrip current next
          valid processed cell remaining headSplit).input_space.trans (by
            simp [flatPackedNormalizationFlatCost])
  output_space := flatPackedNormalizationResultSpace_le_cost column
    periodicStrip current next valid processed remaining split
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction remaining generalizing valid processed with
    | nil =>
        let values := Code.flatPackedTransitionScanState periodicStrip current
          next valid processed.length
        have motifEq : periodicStrip.motif = processed := by simpa using split
        have body := flatPackedNormalizationBodyZero column periodicStrip
          current next valid processed
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    (Code.flatPackedNormalizationStepCode column))
                  continuation)
                (flatCountdownOutput (fun _ => values) 0 values)) := by
          apply EvaluatorExecutionFits.ret_fix_zero
          · rfl
          · simp only [continuationSpace_fix]
            have output := body.output_space
            simp only [flatPackedNormalizationFlatCost] at budget
            simp only [values] at *
            omega
          · simpa [flatCountdownOutput, values, motifEq,
              Code.flatPackedTransitionScanState] using after
        exact body.call
          (.fix
            (Code.flatCountdownBody
              (Code.flatPackedNormalizationStepCode column))
            continuation)
          bound
          (by
            simp only [continuationSpace_fix,
              flatPackedNormalizationFlatCost] at *
            exact budget)
          fixedAfter
    | cons cell remaining induction =>
        let nextValid :=
          valid && current.normalizedAtBool periodicStrip column cell
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
        have body := flatPackedNormalizationBodySucc column periodicStrip
          current next valid processed cell remaining headSplit
        have recursiveBudget :
            flatPackedNormalizationFlatCost column periodicStrip current next
                nextValid nextProcessed remaining +
              continuationSpace continuation ≤ bound := by
          have raw : flatPackedNormalizationFlatCost column periodicStrip
                current next
                (valid && current.normalizedAtBool periodicStrip column cell)
                (processed ++ [cell]) remaining +
              continuationSpace continuation ≤ bound := by
            simp only [flatPackedNormalizationFlatCost] at budget
            omega
          simpa only [nextValid, nextProcessed] using raw
        have recursiveAfter :
            EvaluatorExecutionFits bound
              (.ret continuation
                (Code.flatPackedTransitionScanState periodicStrip current next
                  (nextValid && remaining.all fun tailCell =>
                    current.normalizedAtBool periodicStrip column tailCell)
                  periodicStrip.motif.length)) := by
          simpa [nextValid, Bool.and_assoc] using after
        have recursiveBody := induction nextValid nextProcessed nextSplit
          recursiveBudget recursiveAfter
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody
                    (Code.flatPackedNormalizationStepCode column))
                  continuation)
                (flatCountdownOutput (fun _ => output)
                  (remaining.length + 1) values)) := by
          apply EvaluatorExecutionFits.ret_fix_succ
          · simp [flatCountdownOutput, output, nextValid]
          · simp only [continuationSpace_fix]
            have outputSpace := body.output_space
            simp only [flatPackedNormalizationFlatCost] at budget
            simp only [values, output, nextValid, nextProcessed] at *
            omega
          · simpa [flatCountdownOutput, output, nextValid,
              nextProcessed] using recursiveBody
        exact body.call
          (.fix
            (Code.flatCountdownBody
              (Code.flatPackedNormalizationStepCode column))
            continuation)
          bound
          (by
            simp only [continuationSpace_fix]
            simp only [flatPackedNormalizationFlatCost] at budget
            omega)
          fixedAfter

/-! ## Native polynomial bounds -/

def flatPackedNormalizationContextUnit
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next) + 10

def flatPackedNormalizationContextCore
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000000000000000000 *
    (flatPackedNormalizationContextUnit periodicStrip current next) ^ 2

def flatPackedNormalizationBodySpaceBound
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) : Nat :=
  10000000000000000000000000000000000000000000000000000000000000000000000000000000000 *
    (flatPackedNormalizationContextUnit periodicStrip current next) ^ 2

theorem flatPackedNormalizationContextCore_large
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) :
    1000000 * flatPackedNormalizationContextUnit periodicStrip current next +
        1000 ≤
      flatPackedNormalizationContextCore periodicStrip current next := by
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  have positive : 10 ≤ unit := by
    simp [unit, flatPackedNormalizationContextUnit]
  have squareDominates : unit ≤ unit ^ 2 := by nlinarith
  simp only [flatPackedNormalizationContextCore]
  change 1000000 * unit + 1000 ≤ _ * unit ^ 2
  omega

theorem flatPackedNormalizationScanUnit_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (index : Nat) (indexBound : index ≤ periodicStrip.motif.length) :
    flatPackedNormalizationAtUnit
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          index) ≤
      2 * flatPackedNormalizationContextUnit periodicStrip current next := by
  let context := Code.flatPackedTransitionContext periodicStrip current next
  have indexBits := listCodeEncodeNat_length_mono indexBound
  have motifMember : periodicStrip.motif.length ∈ context := by
    simp [context, Code.flatPackedTransitionContext]
  have motifSpace := flatPackedTransitionScanMemberSpace_le
    periodicStrip.motif.length context motifMember
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases valid <;>
    simp [flatPackedNormalizationAtUnit,
      flatPackedNormalizationContextUnit,
      Code.flatPackedTransitionScanState,
      Code.flatPackedTransitionContext, context,
      encodedListSpace_cons, zeroBits, oneBits] at * <;>
    omega

theorem flatPackedNormalizedAtCost_le_context_core
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizedAtCost column periodicStrip current next valid
        processed cell ≤
      flatPackedNormalizationContextCore periodicStrip current next := by
  have localCost := flatPackedNormalizedAtCost_le_bound column periodicStrip
    current next valid processed cell remaining split
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have unit := flatPackedNormalizationScanUnit_le_context periodicStrip current
    next valid processed.length indexBound
  calc
    flatPackedNormalizedAtCost column periodicStrip current next valid
        processed cell ≤
      flatPackedNormalizedAtSpaceBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := localCost
    _ ≤ 100000000000000000000000000000000000000000000000000000000000000000000000 *
        (2 * flatPackedNormalizationContextUnit periodicStrip current next) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left unit 2)
    _ ≤ flatPackedNormalizationContextCore periodicStrip current next := by
      simp [flatPackedNormalizationContextCore]
      ring_nf
      omega

theorem flatPackedNormalizationGetCost_le_context_core
    (index : Nat) (fixed : index ≤ 2)
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    getCost index
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedNormalizationContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid scanIndex
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  have scanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid scanIndex indexBound
  have scanSpace : encodedListSpace values + 1 ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have raw := listCodeGetCost_le_linear index values
  calc
    getCost index values ≤
        (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
    _ ≤ 30000 * (2 * unit) := by
      gcongr
      omega
    _ ≤ flatPackedNormalizationContextCore periodicStrip current next := by
      simp [flatPackedNormalizationContextCore, unit]
      nlinarith

theorem flatPackedNormalizationDropTwoCost_le_context_core
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (scanIndex : Nat)
    (indexBound : scanIndex ≤ periodicStrip.motif.length) :
    dropCost 2
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          scanIndex) ≤
      flatPackedNormalizationContextCore periodicStrip current next := by
  have whole := flatPackedNormalizationGetCost_le_context_core 2 (by omega)
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

set_option maxHeartbeats 1000000 in
theorem flatPackedNormalizationUpdatedValidCost_le_context
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizationUpdatedValidCost column periodicStrip current next
        valid processed cell ≤
      2000 * flatPackedNormalizationContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let core := flatPackedNormalizationContextCore periodicStrip current next
  have indexBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have scanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid processed.length indexBound
  have scanSpace : encodedListSpace values + 10 ≤ 2 * unit := by
    simpa [values, unit, flatPackedNormalizationAtUnit] using scanUnit
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedNormalizationContextUnit]
  have squareDominates : unit ≤ unit ^ 2 := by nlinarith
  have coreLarge : 2 * unit + 1 ≤ core := by
    simp only [core, flatPackedNormalizationContextCore]
    change 2 * unit + 1 ≤ _ * unit ^ 2
    omega
  have valuesBound : encodedListSpace values ≤ core := by
    omega
  have get0 := flatPackedNormalizationGetCost_le_context_core 0 (by omega)
    periodicStrip current next valid processed.length indexBound
  have atCost := flatPackedNormalizedAtCost_le_context_core column
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
    (current.normalizedAtBool periodicStrip column cell).toNat
    (getCost 0 values)
    (flatPackedNormalizedAtCost column periodicStrip current next valid
      processed cell)
    core (Bool.toNat_le _) (Bool.toNat_le _) valuesBound headBound
      headSuccessorBound (by simpa [values, core] using get0)
      (by simpa [core] using atCost) positive
  have exact : flatPackedNormalizationUpdatedValidCost column periodicStrip
      current next valid processed cell ≤ 1000 * (core + 1) := by
    simpa [flatPackedNormalizationUpdatedValidCost, values] using wrapped
  exact exact.trans (by
    omega)

theorem flatPackedNormalizationIndexCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell)
    (processedBound : processed.length ≤ periodicStrip.motif.length) :
    flatPackedNormalizationIndexCost periodicStrip current next valid
        processed ≤
      2 * flatPackedNormalizationContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let core := flatPackedNormalizationContextCore periodicStrip current next
  have get1 := flatPackedNormalizationGetCost_le_context_core 1 (by omega)
    periodicStrip current next valid processed.length processedBound
  have selected := flatMotifIndexSelectedSpace_le 1 values
  have scanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have selectedSpace : encodedListSpace [processed.length] ≤ 2 * unit := by
    have valueEq : values[1]?.getD 0 = processed.length := by
      simp [values, Code.flatPackedTransitionScanState]
    rw [valueEq] at selected
    simp only [flatPackedNormalizationAtUnit] at scanUnit
    exact selected.trans (by
      simp only [values, unit]
      omega)
  have successorRaw := succCost_le [processed.length]
  have coreLarge := flatPackedNormalizationContextCore_large periodicStrip
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

theorem flatPackedNormalizationIndexAndRestCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) (cell : Cell)
    (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizationIndexAndRestCost periodicStrip current next valid
        processed ≤
      4 * flatPackedNormalizationContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let core := flatPackedNormalizationContextCore periodicStrip current next
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have indexCost := flatPackedNormalizationIndexCost_le_context periodicStrip
    current next valid processed processedBound
  have dropBound := flatPackedNormalizationDropTwoCost_le_context_core
    periodicStrip current next valid processed.length processedBound
  have scanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have nextScanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid (processed.length + 1) nextBound
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at scanUnit
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
    simp [unit, flatPackedNormalizationContextUnit] at motifSpace ⊢
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
      simp only [flatPackedNormalizationAtUnit] at nextScanUnit
      simp only [unit]
      omega)
  have raw := listCodePrependCost_le_of values [processed.length + 1]
    (values.drop 2)
    (flatPackedNormalizationIndexCost periodicStrip current next valid
      processed) (EvaluatorCodeFits.dropCost 2 values) (2 * unit) valuesSpace fieldSpace (by
        simpa only [List.headI_cons] using outputSpace)
  have coreLarge := flatPackedNormalizationContextCore_large periodicStrip
    current next
  have overhead : 6 * unit + 2 ≤ core := by omega
  change prependCost values [processed.length + 1] (values.drop 2)
    (flatPackedNormalizationIndexCost periodicStrip current next valid
      processed) (EvaluatorCodeFits.dropCost 2 values) ≤ 4 * core
  change flatPackedNormalizationIndexCost periodicStrip current next valid
    processed ≤ 2 * core at indexCost
  change EvaluatorCodeFits.dropCost 2 values ≤ core at dropBound
  omega

theorem flatPackedNormalizationStepCost_le_context
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizationStepCost column periodicStrip current next valid
        processed cell ≤
      2005 * flatPackedNormalizationContextCore periodicStrip current next := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let core := flatPackedNormalizationContextCore periodicStrip current next
  let nextValid := valid && current.normalizedAtBool periodicStrip column cell
  have processedBound : processed.length ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have nextBound : processed.length + 1 ≤ periodicStrip.motif.length := by
    rw [split]
    simp
  have updated := flatPackedNormalizationUpdatedValidCost_le_context column
    periodicStrip current next valid processed cell remaining split
  have rest := flatPackedNormalizationIndexAndRestCost_le_context periodicStrip
    current next valid processed cell remaining split
  have scanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have nextScanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next nextValid (processed.length + 1) nextBound
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at scanUnit
    simp only [values, unit]
    omega
  have fieldSpace : encodedListSpace [nextValid.toNat] ≤ 2 * unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases nextValid with
    | false =>
        simp [unit, flatPackedNormalizationContextUnit,
          encodedListSpace_cons, zeroBits]
        omega
    | true =>
        simp [unit, flatPackedNormalizationContextUnit,
          encodedListSpace_cons, oneBits]
  have outputSpace : encodedListSpace
      (Code.flatPackedTransitionScanState periodicStrip current next nextValid
        (processed.length + 1)) ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at nextScanUnit
    simp only [unit]
    omega
  have raw := listCodePrependCost_le_of values [nextValid.toNat]
    ((processed.length + 1) :: values.drop 2)
    (flatPackedNormalizationUpdatedValidCost column periodicStrip current next
      valid processed cell)
    (flatPackedNormalizationIndexAndRestCost periodicStrip current next valid
      processed) (2 * unit) valuesSpace fieldSpace (by
        simpa [nextValid, values, Code.flatPackedTransitionScanState] using
          outputSpace)
  have coreLarge := flatPackedNormalizationContextCore_large periodicStrip
    current next
  have overhead : 6 * unit + 2 ≤ core := by omega
  change prependCost values [nextValid.toNat]
      ((processed.length + 1) :: values.drop 2)
      (flatPackedNormalizationUpdatedValidCost column periodicStrip current next
        valid processed cell)
      (flatPackedNormalizationIndexAndRestCost periodicStrip current next valid
        processed) ≤ 2005 * core
  change flatPackedNormalizationUpdatedValidCost column periodicStrip current
    next valid processed cell ≤ 2000 * core at updated
  change flatPackedNormalizationIndexAndRestCost periodicStrip current next
    valid processed ≤ 4 * core at rest
  omega

theorem flatPackedNormalizationBodySuccCost_le_context
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizationBodySuccCost column periodicStrip current next valid
        processed cell remaining.length ≤
      flatPackedNormalizationBodySpaceBound periodicStrip current next := by
  let payload := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let nextValid := valid && current.normalizedAtBool periodicStrip column cell
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    nextValid (processed.length + 1)
  let values := remaining.length :: payload
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let core := flatPackedNormalizationContextCore periodicStrip current next
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
    simp [unit, flatPackedNormalizationContextUnit]
  have payloadUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have outputUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next nextValid (processed.length + 1) nextBound
  have payloadSpace : encodedListSpace payload ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at payloadUnit
    simp only [payload, unit]
    omega
  have outputSpace : encodedListSpace output ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at outputUnit
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
    simp [unit, flatPackedNormalizationContextUnit] at motifSpace ⊢
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
  have coreLarge := flatPackedNormalizationContextCore_large periodicStrip
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
  have step := flatPackedNormalizationStepCost_le_context column periodicStrip
    current next valid processed cell remaining split
  change flatPackedNormalizationStepCost column periodicStrip current next valid
    processed cell ≤ 2005 * core at step
  let transformedCost :=
    flatPackedNormalizationStepCost column periodicStrip current next valid
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
        flatPackedNormalizationContextUnit]
      omega)
    (by simpa only [List.headI_cons] using taggedOutputSpace)
  have branchBound : flatCountdownSuccBranchCost (fun _ => output)
      (fun _ => flatPackedNormalizationStepCost column periodicStrip current
        next valid processed cell) remaining.length payload ≤
      2010 * core := by
    change prependCost values [1] (remaining.length :: output)
      (oneCost values) payloadCost ≤ 2010 * core
    omega
  have bodyBound : flatPackedNormalizationBodySuccCost column periodicStrip
      current next valid processed cell remaining.length ≤ 2011 * core := by
    simp only [flatPackedNormalizationBodySuccCost, flatCountdownBodyCost]
    change flatCountdownSuccBranchCost (fun _ => output)
        (fun _ => flatPackedNormalizationStepCost column periodicStrip current
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
    flatPackedNormalizationBodySuccCost column periodicStrip current next valid
        processed cell remaining.length ≤ 2011 * core := bodyBound
    _ ≤ flatPackedNormalizationBodySpaceBound periodicStrip current next := by
      simp [core, flatPackedNormalizationContextCore,
        flatPackedNormalizationBodySpaceBound]
      ring_nf
      omega

theorem flatPackedNormalizationBodyZeroCost_le_context
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell)
    (processedBound : processed.length ≤ periodicStrip.motif.length) :
    flatPackedNormalizationBodyZeroCost periodicStrip current next valid
        processed ≤
      flatPackedNormalizationBodySpaceBound periodicStrip current next := by
  let payload := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  have scanUnit := flatPackedNormalizationScanUnit_le_context periodicStrip
    current next valid processed.length processedBound
  have payloadSpace : encodedListSpace payload ≤ 2 * unit := by
    simp only [flatPackedNormalizationAtUnit] at scanUnit
    simp only [payload, unit]
    omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have coreLarge := flatPackedNormalizationContextCore_large periodicStrip
    current next
  have coreToBody : flatPackedNormalizationContextCore periodicStrip current
      next ≤ flatPackedNormalizationBodySpaceBound periodicStrip current
      next := by
    simp [flatPackedNormalizationContextCore,
      flatPackedNormalizationBodySpaceBound]
    ring_nf
    omega
  change zeroPrimeCost payload + encodedListSpace (0 :: payload) +
      encodedListSpace (0 :: payload) + 1 ≤
    flatPackedNormalizationBodySpaceBound periodicStrip current next
  have localBound : zeroPrimeCost payload + encodedListSpace (0 :: payload) +
      encodedListSpace (0 :: payload) + 1 ≤
      flatPackedNormalizationContextCore periodicStrip current next := by
    simp [zeroPrimeCost, encodedListSpace_cons, zeroBits]
    omega
  exact localBound.trans coreToBody

theorem flatPackedNormalizationFlatCost_le_body_mul
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    flatPackedNormalizationFlatCost column periodicStrip current next valid
        processed remaining ≤
      flatPackedNormalizationBodySpaceBound periodicStrip current next *
        (remaining.length + 1) := by
  induction remaining generalizing valid processed with
  | nil =>
      have processedBound : processed.length ≤
          periodicStrip.motif.length := by
        have lengths := congrArg List.length split
        simp only [List.append_nil] at lengths
        omega
      simpa [flatPackedNormalizationFlatCost] using
        flatPackedNormalizationBodyZeroCost_le_context periodicStrip current
          next valid processed processedBound
  | cons cell remaining induction =>
      let nextValid :=
        valid && current.normalizedAtBool periodicStrip column cell
      let nextProcessed := processed ++ [cell]
      have headSplit : periodicStrip.motif =
          processed ++ cell :: remaining := by
        simpa [List.append_assoc] using split
      have nextSplit : periodicStrip.motif = nextProcessed ++ remaining := by
        simpa [nextProcessed, List.append_assoc] using split
      have body := flatPackedNormalizationBodySuccCost_le_context column
        periodicStrip current next valid processed cell remaining headSplit
      have tail := induction nextValid nextProcessed nextSplit
      simp only [flatPackedNormalizationFlatCost, List.length_cons]
      simp only [nextValid, nextProcessed] at tail
      nlinarith

theorem flatPackedNormalizationMotifLength_le_contextUnit
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState) :
    periodicStrip.motif.length + 1 ≤
      flatPackedNormalizationContextUnit periodicStrip current next := by
  have lengthBound := list_length_le_encodedListSpace
    (Code.flatPackedTransitionContext periodicStrip current next)
  have contextLength :
      (Code.flatPackedTransitionContext periodicStrip current next).length =
        7 + 2 * periodicStrip.motif.length := by
    simp [Code.flatPackedTransitionContext,
      PeriodicStripFlatEncoding.cellFields, List.length_flatMap]
    omega
  rw [contextLength] at lengthBound
  simp [flatPackedNormalizationContextUnit]
  omega

theorem flatPackedNormalizationFlatCost_le_cubic
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationFlatCost column periodicStrip current next true []
        periodicStrip.motif ≤
      10000000000000000000000000000000000000000000000000000000000000000000000000000000000 *
        (flatPackedNormalizationContextUnit periodicStrip current next) ^ 3 := by
  have additive := flatPackedNormalizationFlatCost_le_body_mul column
    periodicStrip current next true [] periodicStrip.motif (by simp)
  have length := flatPackedNormalizationMotifLength_le_contextUnit
    periodicStrip current next
  calc
    flatPackedNormalizationFlatCost column periodicStrip current next true []
        periodicStrip.motif ≤
      flatPackedNormalizationBodySpaceBound periodicStrip current next *
        (periodicStrip.motif.length + 1) := additive
    _ ≤ flatPackedNormalizationBodySpaceBound periodicStrip current next *
        flatPackedNormalizationContextUnit periodicStrip current next := by
      gcongr
    _ = _ := by
      simp [flatPackedNormalizationBodySpaceBound]
      ring

theorem flatPackedNormalizationFlatBounded
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed remaining : List Cell)
    (split : periodicStrip.motif = processed ++ remaining) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.flatPackedNormalizationStepCode column))
      (remaining.length ::
        Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)
      (Code.flatPackedTransitionScanState periodicStrip current next
        (valid && remaining.all fun cell =>
          current.normalizedAtBool periodicStrip column cell)
        periodicStrip.motif.length)
      (flatPackedNormalizationBodySpaceBound periodicStrip current next *
        (remaining.length + 1)) :=
  (flatPackedNormalizationFlat column periodicStrip current next valid processed
    remaining split).mono
      (flatPackedNormalizationFlatCost_le_body_mul column periodicStrip current
        next valid processed remaining split)

/-! ## Complete column wrapper -/

def flatPackedNormalizationLoopInputCost
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let zeroAndContext := prependCost values [0] values
    (zeroCost values) (idCost values)
  let validIndexAndContext := prependCost values [1] (0 :: values)
    (oneCost values) zeroAndContext
  prependCost values [periodicStrip.motif.length] (1 :: 0 :: values)
    (getCost 2 values) validIndexAndContext

theorem flatPackedNormalizationLoopInput
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits Code.flatPackedNormalizationLoopInputCode
      (Code.flatPackedTransitionContext periodicStrip current next)
      (periodicStrip.motif.length ::
        Code.flatPackedTransitionScanState periodicStrip current next true 0)
      (flatPackedNormalizationLoopInputCost periodicStrip current next) := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  have fitted := prepend (get 2 values)
    (prepend (one values) (prepend (zero values) (id values)))
  simpa [Code.flatPackedNormalizationLoopInputCode,
    flatPackedNormalizationLoopInputCost, values, prependCost,
    Code.flatPackedTransitionContext,
    Code.flatPackedTransitionScanState] using fitted

theorem flatPackedNormalizationLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationLoopInputCost periodicStrip current next ≤
      100000 *
        flatPackedNormalizationContextUnit periodicStrip current next := by
  let values := Code.flatPackedTransitionContext periodicStrip current next
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let zeroAndContext := prependCost values [0] values
    (zeroCost values) (idCost values)
  let validIndexAndContext := prependCost values [1] (0 :: values)
    (oneCost values) zeroAndContext
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedNormalizationContextUnit]
  have valuesSpace : encodedListSpace values ≤ 2 * unit := by
    simp [unit, flatPackedNormalizationContextUnit, values]
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
      flatPackedNormalizationContextUnit, values]
    omega
  have validIndexAndContextSpace :
      encodedListSpace (1 :: 0 :: values) ≤ 2 * unit := by
    simp [encodedListSpace_cons, zeroBits, oneBits, unit,
      flatPackedNormalizationContextUnit, values]
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
      flatPackedNormalizationContextUnit, values] at prefixBound fieldInValues ⊢
    omega
  have identityRaw := flatLookupIdCost_le_linear values
  have identity : idCost values ≤ 10 * unit := by
    exact identityRaw.trans (by
      simp [unit, flatPackedNormalizationContextUnit, values])
  have zeroRaw := listCodeZeroCost_le_linear values
  have zero : zeroCost values ≤ 10000 * unit := by
    exact zeroRaw.trans (by
      simp [unit, flatPackedNormalizationContextUnit, values])
  have oneRaw := flatLookupOneCost_le_linear values
  have one : oneCost values ≤ 20000 * unit := by
    exact oneRaw.trans (by
      simp [unit, flatPackedNormalizationContextUnit, values])
  have getRaw := listCodeGetCost_le_linear 2 values
  have getTwo : getCost 2 values ≤ 30000 * unit := by
    exact getRaw.trans (by
      simp [unit, flatPackedNormalizationContextUnit, values])
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

def flatPackedNormalizationColumnCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.normalizedColumnBool periodicStrip column)
    periodicStrip.motif.length
  getCost 0 output +
    (flatPackedNormalizationFlatCost column periodicStrip current next true []
        periodicStrip.motif +
      flatPackedNormalizationLoopInputCost periodicStrip current next)

theorem flatPackedNormalizationColumn
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedNormalizationColumnCode column)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.normalizedColumnBool periodicStrip column).toNat]
      (flatPackedNormalizationColumnCost column periodicStrip current next) := by
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.normalizedColumnBool periodicStrip column)
    periodicStrip.motif.length
  have loop := flatPackedNormalizationFlat column periodicStrip current next
    true [] periodicStrip.motif (by simp)
  have fitted := comp (get 0 output)
    (comp loop (flatPackedNormalizationLoopInput periodicStrip current next))
  simpa [Code.flatPackedNormalizationColumnCode,
    flatPackedNormalizationColumnCost, output,
    Code.flatPackedTransitionScanState,
    PackedWindowState.normalizedColumnBool] using fitted

def flatPackedNormalizationColumnSpaceBound
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : Nat :=
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  200000 *
    (flatPackedNormalizationBodySpaceBound periodicStrip current next * unit +
      unit + 1)

theorem flatPackedNormalizationColumnCost_le_bound
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedNormalizationColumnCost column periodicStrip current next ≤
      flatPackedNormalizationColumnSpaceBound periodicStrip current next := by
  let unit := flatPackedNormalizationContextUnit periodicStrip current next
  let body := flatPackedNormalizationBodySpaceBound periodicStrip current next
  let scanCost := flatPackedNormalizationFlatCost column periodicStrip current
    next true [] periodicStrip.motif
  let output := Code.flatPackedTransitionScanState periodicStrip current next
    (current.normalizedColumnBool periodicStrip column)
    periodicStrip.motif.length
  have additive := flatPackedNormalizationFlatCost_le_body_mul column
    periodicStrip current next true [] periodicStrip.motif (by simp)
  have length := flatPackedNormalizationMotifLength_le_contextUnit
    periodicStrip current next
  have scanBound : scanCost ≤ body * unit := by
    simp only [scanCost, body, unit]
    calc
      flatPackedNormalizationFlatCost column periodicStrip current next true []
          periodicStrip.motif ≤
        flatPackedNormalizationBodySpaceBound periodicStrip current next *
          (periodicStrip.motif.length + 1) := additive
      _ ≤ _ := by gcongr
  have scanFit := flatPackedNormalizationFlat column periodicStrip current next
    true [] periodicStrip.motif (by simp)
  have outputSpace : encodedListSpace output ≤ scanCost := by
    simpa [output, scanCost, PackedWindowState.normalizedColumnBool] using
      scanFit.output_space
  have projectionRaw := listCodeGetCost_le_linear 0 output
  have projection : getCost 0 output ≤ 10000 * (scanCost + 1) :=
    projectionRaw.trans (by gcongr)
  have input := flatPackedNormalizationLoopInputCost_le_linear periodicStrip
    current next
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedNormalizationContextUnit]
  change getCost 0 output +
      (scanCost + flatPackedNormalizationLoopInputCost periodicStrip current
        next) ≤ 200000 * (body * unit + unit + 1)
  omega

theorem flatPackedNormalizationColumnBounded
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    EvaluatorCodeFits (Code.flatPackedNormalizationColumnCode column)
      (Code.flatPackedTransitionContext periodicStrip current next)
      [(current.normalizedColumnBool periodicStrip column).toNat]
      (flatPackedNormalizationColumnSpaceBound periodicStrip current next) :=
  (flatPackedNormalizationColumn column periodicStrip current next).mono
    (flatPackedNormalizationColumnCost_le_bound column periodicStrip current
      next)

end EvaluatorCodeFits
end PartrecToTM2
end Turing

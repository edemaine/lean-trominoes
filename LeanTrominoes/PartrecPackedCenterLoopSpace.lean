/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPackedCenterBaseSpace
import LeanTrominoes.PartrecPackedCenterLoop
import LeanTrominoes.PartrecPackedNormalizationLoopSpace
import LeanTrominoes.PartrecUnpairSpace

/-!
# Evaluator-space certificate for the packed center-validity loop

This file fits every component of the streaming motif scan and combines the
exact body costs under one reachable-suffix workspace envelope.  A later
majorant theorem can bound this finite envelope by the common polynomial strip
transition budget.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def packedCenterHeadRowCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  getCost 1 [Encodable.encode cell.1, Encodable.encode cell.2] +
    (unpairCost (Encodable.encode cell) +
      packedNormalizationHeadCost periodicStrip packed
        WindowState.center valid cell remaining)

theorem packedCenterHeadRow
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedCenterHeadRowCode
      (Code.packedCenterState periodicStrip packed valid
        (cell :: remaining))
      [Encodable.encode cell.2]
      (packedCenterHeadRowCost periodicStrip packed
        valid cell remaining) := by
  rcases cell with ⟨x, y⟩
  have decoded := comp (unpair (Encodable.encode (x, y)))
    (packedNormalizationHead periodicStrip packed
      WindowState.center valid (x, y) remaining)
  have decoded' :
      EvaluatorCodeFits
        (Code.unpairCode.comp Code.packedNormalizationHeadCode)
        (Code.packedCenterState periodicStrip packed valid
          ((x, y) :: remaining))
        [Encodable.encode x, Encodable.encode y]
        (unpairCost (Encodable.encode (x, y)) +
          packedNormalizationHeadCost periodicStrip packed
            WindowState.center valid (x, y) remaining) := by
    simpa [Code.packedCenterState] using decoded
  have projected := comp
    (get 1 [Encodable.encode x, Encodable.encode y]) decoded'
  simpa [Code.packedCenterHeadRowCode,
    Code.packedCenterState, packedCenterHeadRowCost] using projected

def packedCenterBaseArgumentsCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state := Code.packedCenterState periodicStrip packed valid
    (cell :: remaining)
  let restWord := prependCost state [Encodable.encode cell.2]
    [packed.assignmentWord]
    (packedCenterHeadRowCost periodicStrip packed
      valid cell remaining)
    (getCost 5 state)
  let restHead := prependCost state [Encodable.encode cell]
    [Encodable.encode cell.2, packed.assignmentWord]
    (packedNormalizationHeadCost periodicStrip packed
      WindowState.center valid cell remaining) restWord
  let restMotif := prependCost state
    [Encodable.encode periodicStrip.motif]
    [Encodable.encode cell, Encodable.encode cell.2,
      packed.assignmentWord]
    (getCost 0 state) restHead
  let restPhase := prependCost state [packed.phase]
    [Encodable.encode periodicStrip.motif,
      Encodable.encode cell, Encodable.encode cell.2,
      packed.assignmentWord]
    (getCost 3 state) restMotif
  prependCost state [periodicStrip.period]
    [packed.phase, Encodable.encode periodicStrip.motif,
      Encodable.encode cell, Encodable.encode cell.2,
      packed.assignmentWord]
    (getCost 2 state) restPhase

theorem packedCenterBaseArguments
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.packedCenterBaseArgumentsCode
      (Code.packedCenterState periodicStrip packed valid
        (cell :: remaining))
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        Encodable.encode cell, Encodable.encode cell.2,
        packed.assignmentWord]
      (packedCenterBaseArgumentsCost periodicStrip packed
        valid cell remaining) := by
  let state := Code.packedCenterState periodicStrip packed valid
    (cell :: remaining)
  have restWord := prepend
    (packedCenterHeadRow periodicStrip packed valid cell remaining)
    (get 5 state)
  have restHead := prepend
    (packedNormalizationHead periodicStrip packed
      WindowState.center valid cell remaining) restWord
  have restMotif := prepend (get 0 state) restHead
  have restPhase := prepend (get 3 state) restMotif
  have result := prepend (get 2 state) restPhase
  simpa [Code.packedCenterBaseArgumentsCode,
    packedCenterBaseArgumentsCost, Code.packedCenterState,
    Code.packedNormalizationState, prependCost, state] using result

def packedCenterHeadValidCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  packedCenterBaseValidCost tromino periodicStrip packed cell +
    packedCenterBaseArgumentsCost periodicStrip packed
      valid cell remaining

theorem packedCenterHeadValid
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits (Code.packedCenterHeadValidCode tromino)
      (Code.packedCenterState periodicStrip packed valid
        (cell :: remaining))
      [((packed.centerBaseInsideBool tromino periodicStrip cell) &&
        packed.centerBaseCoveredBool tromino periodicStrip cell).toNat]
      (packedCenterHeadValidCost tromino periodicStrip packed
        valid cell remaining) := by
  simpa [Code.packedCenterHeadValidCode,
    packedCenterHeadValidCost] using
    comp
      (packedCenterBaseValid tromino periodicStrip
        wellFormed packed cell)
      (packedCenterBaseArguments periodicStrip packed
        valid cell remaining)

def packedCenterUpdatedValidCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state := Code.packedCenterState periodicStrip packed valid
    (cell :: remaining)
  let cellTag :=
    (packed.centerBaseInsideBool tromino periodicStrip cell &&
      packed.centerBaseCoveredBool tromino periodicStrip cell).toNat
  boolAndCost state valid.toNat cellTag
    (getCost 6 state)
    (packedCenterHeadValidCost tromino periodicStrip packed
      valid cell remaining)

theorem packedCenterUpdatedValid
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits (Code.packedCenterUpdatedValidCode tromino)
      (Code.packedCenterState periodicStrip packed valid
        (cell :: remaining))
      [(valid &&
        (packed.centerBaseInsideBool tromino periodicStrip cell &&
          packed.centerBaseCoveredBool
            tromino periodicStrip cell)).toNat]
      (packedCenterUpdatedValidCost tromino periodicStrip packed
        valid cell remaining) := by
  have combined := boolAnd
    (get 6 (Code.packedCenterState periodicStrip packed valid
      (cell :: remaining)))
    (packedCenterHeadValid tromino periodicStrip wellFormed
      packed valid cell remaining)
  cases valid <;>
    cases inside :
      packed.centerBaseInsideBool tromino periodicStrip cell <;>
    cases covered :
      packed.centerBaseCoveredBool tromino periodicStrip cell <;>
    simpa [Code.packedCenterUpdatedValidCode,
      packedCenterUpdatedValidCost, Code.packedCenterState,
      Code.packedNormalizationState, inside, covered] using combined

def packedCenterConsStepCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state := Code.packedCenterState periodicStrip packed valid
    (cell :: remaining)
  let nextValid := valid &&
    (packed.centerBaseInsideBool tromino periodicStrip cell &&
      packed.centerBaseCoveredBool tromino periodicStrip cell)
  let restWord := prependCost state [packed.assignmentWord]
    [nextValid.toNat] (getCost 5 state)
    (packedCenterUpdatedValidCost tromino periodicStrip packed
      valid cell remaining)
  let restColumn := prependCost state [WindowState.center.val]
    [packed.assignmentWord, nextValid.toNat]
    (getCost 4 state) restWord
  let restPhase := prependCost state [packed.phase]
    [WindowState.center.val, packed.assignmentWord,
      nextValid.toNat]
    (getCost 3 state) restColumn
  let restPeriod := prependCost state [periodicStrip.period]
    [packed.phase, WindowState.center.val,
      packed.assignmentWord, nextValid.toNat]
    (getCost 2 state) restPhase
  let restTail := prependCost state [Encodable.encode remaining]
    [periodicStrip.period, packed.phase, WindowState.center.val,
      packed.assignmentWord, nextValid.toNat]
    (packedNormalizationTailCost periodicStrip packed
      WindowState.center valid cell remaining) restPeriod
  prependCost state [Encodable.encode periodicStrip.motif]
    [Encodable.encode remaining, periodicStrip.period,
      packed.phase, WindowState.center.val,
      packed.assignmentWord, nextValid.toNat]
    (getCost 0 state) restTail

theorem packedCenterConsStep
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    let nextValid := valid &&
      (packed.centerBaseInsideBool tromino periodicStrip cell &&
        packed.centerBaseCoveredBool tromino periodicStrip cell)
    EvaluatorCodeFits (Code.packedCenterConsStepCode tromino)
      (Code.packedCenterState periodicStrip packed valid
        (cell :: remaining))
      (Code.packedCenterState periodicStrip packed
        nextValid remaining)
      (packedCenterConsStepCost tromino periodicStrip packed
        valid cell remaining) := by
  simp only
  let state := Code.packedCenterState periodicStrip packed valid
    (cell :: remaining)
  have restWord := prepend (get 5 state)
    (packedCenterUpdatedValid tromino periodicStrip wellFormed
      packed valid cell remaining)
  have restColumn := prepend (get 4 state) restWord
  have restPhase := prepend (get 3 state) restColumn
  have restPeriod := prepend (get 2 state) restPhase
  have restTail := prepend
    (packedNormalizationTail periodicStrip packed
      WindowState.center valid cell remaining) restPeriod
  have result := prepend (get 0 state) restTail
  simpa [Code.packedCenterConsStepCode,
    packedCenterConsStepCost, Code.packedCenterState,
    Code.packedNormalizationState, prependCost, state] using result

def packedCenterStepCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool) : List Cell -> Nat
  | [] =>
      let state := Code.packedCenterState periodicStrip packed valid []
      branchZeroZeroCost state state 0
        (getCost 1 state) (idCost state)
  | cell :: remaining =>
      let state := Code.packedCenterState periodicStrip packed valid
        (cell :: remaining)
      let nextValid := valid &&
        (packed.centerBaseInsideBool tromino periodicStrip cell &&
          packed.centerBaseCoveredBool tromino periodicStrip cell)
      branchZeroSuccCost state
        (Code.packedCenterState periodicStrip packed
          nextValid remaining)
        (Encodable.encode (cell :: remaining))
        (getCost 1 state)
        (packedCenterConsStepCost tromino periodicStrip packed
          valid cell remaining)

theorem packedCenterStep
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (valid : Bool)
    (remaining : List Cell) :
    EvaluatorCodeFits (Code.packedCenterStepCode tromino)
      (Code.packedCenterState periodicStrip packed valid remaining)
      (Code.packedCenterNativeStep tromino periodicStrip packed
        (Code.packedCenterState periodicStrip packed valid remaining))
      (packedCenterStepCost tromino periodicStrip packed
        valid remaining) := by
  cases remaining with
  | nil =>
      simpa [Code.packedCenterStepCode, packedCenterStepCost] using
        branchZero_zero rfl
          (get 1 (Code.packedCenterState periodicStrip packed valid []))
          (id (Code.packedCenterState periodicStrip packed valid []))
  | cons cell remaining =>
      have positive : 0 < Encodable.encode (cell :: remaining) := by simp
      simpa [Code.packedCenterStepCode, packedCenterStepCost] using
        branchZero_succ positive
          (get 1 (Code.packedCenterState periodicStrip packed valid
            (cell :: remaining)))
          (packedCenterConsStep tromino periodicStrip wellFormed
            packed valid cell remaining)

def packedCenterBodyCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) : Nat :=
  flatCountdownBodyCost
    (Code.packedCenterNativeStep tromino periodicStrip packed)
    (fun _ => packedCenterStepCost tromino periodicStrip packed
      valid remaining)
    countdown
    (Code.packedCenterState periodicStrip packed valid remaining)

theorem packedCenterBody
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState)
    (countdown : Nat) (valid : Bool)
    (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody (Code.packedCenterStepCode tromino))
      (countdown ::
        Code.packedCenterState periodicStrip packed valid remaining)
      (flatCountdownOutput
        (Code.packedCenterNativeStep tromino periodicStrip packed)
        countdown
        (Code.packedCenterState periodicStrip packed valid remaining))
      (packedCenterBodyCost tromino periodicStrip packed
        countdown valid remaining) := by
  cases countdown with
  | zero =>
      simpa [Code.flatCountdownBody, flatCountdownOutput,
        packedCenterBodyCost, flatCountdownBodyCost,
        zeroPrimeCost] using
        EvaluatorCodeFits.case_zero
          (successorBranch :=
            .cons Code.one (.cons Code.head
              ((Code.packedCenterStepCode tromino).comp Code.tail)))
          (values := 0 :: Code.packedCenterState
            periodicStrip packed valid remaining)
          (by rfl)
          (zero'_named (Code.packedCenterState
            periodicStrip packed valid remaining))
  | succ countdown =>
      let payload := Code.packedCenterState
        periodicStrip packed valid remaining
      let values := countdown :: payload
      have transformed := comp
        (packedCenterStep tromino periodicStrip wellFormed
          packed valid remaining)
        (tail_named values)
      have payloadResult := prepend (head values) transformed
      have branch := prepend (one values) payloadResult
      simpa [Code.flatCountdownBody, flatCountdownOutput,
        packedCenterBodyCost, flatCountdownBodyCost,
        flatCountdownSuccBranchCost, payload, values,
        prependCost, Code.prepend] using
        EvaluatorCodeFits.case_succ
          (zeroBranch := Code.zero')
          (values := (countdown + 1) :: payload)
          (predecessor := countdown) (by rfl) branch

/-- Maximum of the already-polynomial one-base envelopes over a motif. -/
def packedCenterBaseSpaceMaximum
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : List Cell → Nat
  | [] => 0
  | cell :: cells => max
      (packedCenterBaseValidSpaceBound tromino
        periodicStrip packed cell)
      (packedCenterBaseSpaceMaximum tromino
        periodicStrip packed cells)

theorem packedCenterBaseValidSpaceBound_le_maximum
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (cell : Cell) (cells : List Cell)
    (member : cell ∈ cells) :
    packedCenterBaseValidSpaceBound tromino
        periodicStrip packed cell ≤
      packedCenterBaseSpaceMaximum tromino
        periodicStrip packed cells := by
  induction cells with
  | nil => simp at member
  | cons head cells induction =>
      simp only [List.mem_cons] at member
      simp only [packedCenterBaseSpaceMaximum]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (induction member).trans (Nat.le_max_right _ _)

theorem packedCenter_encode_member_le_list
    (cell : Cell) (cells : List Cell) (member : cell ∈ cells) :
    Encodable.encode cell ≤ Encodable.encode cells := by
  induction cells with
  | nil => simp at member
  | cons head cells induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change Encodable.encode cell ≤
          Nat.pair (Encodable.encode cell) (Encodable.encode cells) + 1
        have paired := Nat.left_le_pair
          (Encodable.encode cell) (Encodable.encode cells)
        omega
      · have tail := encode_list_suffix_le [head] cells
        exact (induction member).trans (by
          simpa only [List.singleton_append] using tail)

theorem packedCenterCandidateInputUnit_le_normalizationInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (member : base ∈ periodicStrip.motif) :
    packedCenterCandidateInputUnit periodicStrip packed base ≤
      3 * packedNormalizationInputUnit periodicStrip packed := by
  have baseCode := packedCenter_encode_member_le_list
    base periodicStrip.motif member
  have baseBits := encodeNat_length_mono baseCode
  have rowCode : Encodable.encode base.2 ≤ Encodable.encode base := by
    change Encodable.encode base.2 ≤
      Nat.pair (Encodable.encode base.1) (Encodable.encode base.2)
    exact Nat.right_le_pair _ _
  have rowBits := encodeNat_length_mono rowCode
  simp only [packedCenterCandidateInputUnit,
    Code.packedCenterCandidateInput, packedNormalizationInputUnit,
    encodedListSpace_cons, encodedListSpace_nil]
  omega

def packedCenterBaseMaximumLinearCoefficient (tromino : Tromino) : Nat :=
  packedCenterBaseValidLinearCoefficient tromino * 3

set_option maxRecDepth 100000 in
theorem packedCenterBaseSpaceMaximum_le_input_of_subset
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (cells : List Cell)
    (subset : ∀ cell ∈ cells, cell ∈ periodicStrip.motif) :
    packedCenterBaseSpaceMaximum tromino periodicStrip packed cells ≤
      packedCenterBaseMaximumLinearCoefficient tromino *
        packedNormalizationInputUnit periodicStrip packed := by
  induction cells with
  | nil => simp [packedCenterBaseSpaceMaximum]
  | cons cell cells induction =>
      have member := subset cell (by simp)
      have tailSubset : ∀ remaining ∈ cells,
          remaining ∈ periodicStrip.motif := by
        intro remaining remainingMember
        exact subset remaining (by simp [remainingMember])
      have tail := induction tailSubset
      have base := packedCenterBaseValidSpaceBound_le_input
        tromino periodicStrip packed cell
      have input := packedCenterCandidateInputUnit_le_normalizationInput
        periodicStrip packed cell member
      have head :
          packedCenterBaseValidSpaceBound tromino periodicStrip packed cell ≤
            packedCenterBaseMaximumLinearCoefficient tromino *
              packedNormalizationInputUnit periodicStrip packed := by
        calc
          _ ≤ packedCenterBaseValidLinearCoefficient tromino *
                packedCenterCandidateInputUnit periodicStrip packed cell :=
            base
          _ ≤ packedCenterBaseValidLinearCoefficient tromino *
                (3 * packedNormalizationInputUnit periodicStrip packed) :=
            Nat.mul_le_mul_left _ input
          _ = packedCenterBaseMaximumLinearCoefficient tromino *
                packedNormalizationInputUnit periodicStrip packed := by
            rw [packedCenterBaseMaximumLinearCoefficient]
            exact (Nat.mul_assoc _ _ _).symm
      simp only [packedCenterBaseSpaceMaximum]
      exact max_le head tail

theorem packedCenterBaseSpaceMaximum_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterBaseSpaceMaximum tromino periodicStrip packed
        periodicStrip.motif ≤
      packedCenterBaseMaximumLinearCoefficient tromino *
        packedNormalizationInputUnit periodicStrip packed := by
  apply packedCenterBaseSpaceMaximum_le_input_of_subset
  intro cell member
  exact member

def packedCenterPolynomialSpaceLimit
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let motifCode := Encodable.encode periodicStrip.motif
  4096 * (periodicStrip.period + packed.phase +
    motifCode + motifCode + motifCode + motifCode +
    motifCode + motifCode + motifCode +
    WindowState.center.val + packed.assignmentWord + 100) + 2000

def packedCenterPolynomialSpaceUnit
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  packedCenterBaseSpaceMaximum tromino periodicStrip packed
      periodicStrip.motif +
    packedNormalizationPolynomialSpaceBound periodicStrip packed
      WindowState.center +
    (encodedListSpace
      [packedCenterPolynomialSpaceLimit periodicStrip packed] + 1)

def packedCenterPolynomialSpaceUnitLinearCoefficient
    (tromino : Tromino) : Nat :=
  packedCenterBaseMaximumLinearCoefficient tromino +
    (1000000000000000000000000000000000 * 100) + 100

set_option maxRecDepth 100000 in
theorem packedCenterPolynomialSpaceUnit_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterPolynomialSpaceUnit tromino periodicStrip packed ≤
      packedCenterPolynomialSpaceUnitLinearCoefficient tromino *
        packedNormalizationInputUnit periodicStrip packed := by
  have bases := packedCenterBaseSpaceMaximum_le_input
    tromino periodicStrip packed
  have normalization := packedNormalizationPolynomialSpaceBound_le_input
    periodicStrip packed WindowState.center
  have nativeRaw := packedNormalizationPolynomialEnvelopeUnit_le_linear
    periodicStrip packed WindowState.center
  have native :
      encodedListSpace
          [packedCenterPolynomialSpaceLimit periodicStrip packed] + 1 ≤
        100 * packedNormalizationInputUnit periodicStrip packed := by
    simpa [packedCenterPolynomialSpaceLimit] using nativeRaw
  change
    packedCenterBaseSpaceMaximum tromino periodicStrip packed
          periodicStrip.motif +
        packedNormalizationPolynomialSpaceBound periodicStrip packed
          WindowState.center +
        (encodedListSpace
          [packedCenterPolynomialSpaceLimit periodicStrip packed] + 1) ≤ _
  calc
    _ ≤ packedCenterBaseMaximumLinearCoefficient tromino *
            packedNormalizationInputUnit periodicStrip packed +
          (1000000000000000000000000000000000 * 100) *
            packedNormalizationInputUnit periodicStrip packed +
          100 * packedNormalizationInputUnit periodicStrip packed :=
      Nat.add_le_add (Nat.add_le_add bases normalization) native
    _ = packedCenterPolynomialSpaceUnitLinearCoefficient tromino *
          packedNormalizationInputUnit periodicStrip packed := by
      rw [packedCenterPolynomialSpaceUnitLinearCoefficient]
      ring

def packedCenterPolynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  10000000000000000000000000000000000000000 *
    packedCenterPolynomialSpaceUnit tromino periodicStrip packed

def packedCenterPolynomialSpaceBoundLinearCoefficient
    (tromino : Tromino) : Nat :=
  10000000000000000000000000000000000000000 *
    packedCenterPolynomialSpaceUnitLinearCoefficient tromino

theorem packedCenterPolynomialSpaceBound_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterPolynomialSpaceBound tromino periodicStrip packed ≤
      packedCenterPolynomialSpaceBoundLinearCoefficient tromino *
        packedNormalizationInputUnit periodicStrip packed := by
  have unit := packedCenterPolynomialSpaceUnit_le_input
    tromino periodicStrip packed
  change
    10000000000000000000000000000000000000000 *
        packedCenterPolynomialSpaceUnit tromino periodicStrip packed ≤ _
  calc
    _ ≤ 10000000000000000000000000000000000000000 *
          (packedCenterPolynomialSpaceUnitLinearCoefficient tromino *
            packedNormalizationInputUnit periodicStrip packed) :=
      Nat.mul_le_mul_left _ unit
    _ = _ := by
      rw [packedCenterPolynomialSpaceBoundLinearCoefficient]
      exact (Nat.mul_assoc _ _ _).symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
theorem packedCenterBodyCost_le_polynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown : Nat) (valid : Bool)
    (remaining leading : List Cell)
    (countdownBound : countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedCenterBodyCost tromino periodicStrip packed
        countdown valid remaining ≤
      packedCenterPolynomialSpaceBound tromino periodicStrip packed := by
  let motifCode := Encodable.encode periodicStrip.motif
  let remainingCode := Encodable.encode remaining
  let limit := packedCenterPolynomialSpaceLimit periodicStrip packed
  let nativeUnit := encodedListSpace [limit] + 1
  let unit := packedCenterPolynomialSpaceUnit
    tromino periodicStrip packed
  change packedCenterBodyCost tromino periodicStrip packed
      countdown valid remaining ≤
    10000000000000000000000000000000000000000 * unit
  have remainingBound : remainingCode ≤ motifCode := by
    simp only [remainingCode, motifCode]
    rw [suffix]
    exact encode_list_suffix_le leading remaining
  have countdownLimit : countdown ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
    omega
  have motifLimit : motifCode ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
    omega
  have remainingLimit : remainingCode ≤ limit :=
    remainingBound.trans motifLimit
  have periodLimit : periodicStrip.period ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
    omega
  have phaseLimit : packed.phase ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
    omega
  have columnLimit : WindowState.center.val ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
    omega
  have wordLimit : packed.assignmentWord ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
    omega
  have countdownBits := listCodeEncodeNat_length_mono countdownLimit
  have countdownPredBits := listCodeEncodeNat_length_mono
    ((Nat.pred_le countdown).trans countdownLimit)
  have motifBits := listCodeEncodeNat_length_mono motifLimit
  have remainingBits := listCodeEncodeNat_length_mono remainingLimit
  have periodBits := listCodeEncodeNat_length_mono periodLimit
  have phaseBits := listCodeEncodeNat_length_mono phaseLimit
  have columnBits := listCodeEncodeNat_length_mono columnLimit
  have wordBits := listCodeEncodeNat_length_mono wordLimit
  have countdownSuccBits := listCodeEncodeNat_length_mono
    (show countdown + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have motifSuccBits := listCodeEncodeNat_length_mono
    (show motifCode + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have remainingSuccBits := listCodeEncodeNat_length_mono
    (show remainingCode + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have periodSuccBits := listCodeEncodeNat_length_mono
    (show periodicStrip.period + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have phaseSuccBits := listCodeEncodeNat_length_mono
    (show packed.phase + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have columnSuccBits := listCodeEncodeNat_length_mono
    (show WindowState.center.val + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have wordSuccBits := listCodeEncodeNat_length_mono
    (show packed.assignmentWord + 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have oneLimitBits := listCodeEncodeNat_length_mono
    (show 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
      omega)
  have positiveLimitBits :
      1 ≤ (Computability.encodeNat limit).length := by
    simpa [oneBits] using oneLimitBits
  have validBits :
      (Computability.encodeNat valid.toNat).length ≤
        (Computability.encodeNat limit).length := by
    cases valid
    · simp [zeroBits]
    · simpa [oneBits] using positiveLimitBits
  have nativeUnitLe : nativeUnit ≤ unit := by
    simp only [nativeUnit, unit, packedCenterPolynomialSpaceUnit,
      limit]
    omega
  cases remaining with
  | nil =>
      have nextStateSpace :
          encodedListSpace
              (Code.packedCenterNativeStep tromino periodicStrip packed
                (Code.packedCenterState periodicStrip packed valid [])) ≤
            10 * ((Computability.encodeNat limit).length + 2) := by
        rw [Code.packedCenterNativeStep_state_nil]
        cases valid <;>
          simp [Code.packedCenterState,
            Code.packedNormalizationState,
            encodedListSpace_cons, encodedListSpace_nil,
            motifCode, zeroBits, oneBits] at * <;>
          omega
      cases countdown <;> cases valid <;>
        simp [packedCenterBodyCost, packedCenterStepCost,
          flatCountdownBodyCost, flatCountdownSuccBranchCost,
          branchZeroZeroCost, branchZeroTestCost,
          prependCost, getCost, dropCost, idCost, headCost,
          nilCost, oneCost, zeroCost, zeroPrimeCost,
          tailCost, succCost, Code.packedCenterState,
          Code.packedNormalizationState,
          encodedListSpace_cons, encodedListSpace_nil,
          motifCode, remainingCode, limit, nativeUnit,
          zeroBits, oneBits, twoBits] at * <;>
        clear * - countdownBits countdownPredBits motifBits
          remainingBits periodBits phaseBits columnBits wordBits
          countdownSuccBits motifSuccBits remainingSuccBits
          periodSuccBits phaseSuccBits columnSuccBits wordSuccBits
          nextStateSpace nativeUnitLe <;>
        omega
  | cons cell remaining =>
      let cellCode := Encodable.encode cell
      let tailCode := Encodable.encode remaining
      have cellRemaining :
          cellCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons, cellCode]
        exact (Nat.left_le_pair cellCode tailCode).trans (Nat.le_succ _)
      have tailRemaining :
          tailCode ≤ Encodable.encode (cell :: remaining) := by
        simp only [Encodable.encode_list_cons, tailCode]
        exact (Nat.right_le_pair cellCode tailCode).trans (Nat.le_succ _)
      have cellLimit : cellCode ≤ limit :=
        cellRemaining.trans (by simpa [remainingCode] using remainingLimit)
      have tailLimit : tailCode ≤ limit :=
        tailRemaining.trans (by simpa [remainingCode] using remainingLimit)
      have cellBits := listCodeEncodeNat_length_mono cellLimit
      have tailBits := listCodeEncodeNat_length_mono tailLimit
      have constructorBits := listCodeEncodeNat_length_mono
        (show Nat.pair cellCode tailCode ≤ limit by
          exact (Nat.le_succ _).trans
            (by simpa [remainingCode] using remainingLimit))
      have cellSuccLimit : cellCode + 1 ≤ limit := by
        simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
        omega
      have tailSuccLimit : tailCode + 1 ≤ limit := by
        simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
        omega
      have cellSuccBits := listCodeEncodeNat_length_mono cellSuccLimit
      have tailSuccBits := listCodeEncodeNat_length_mono tailSuccLimit
      have firstCodeCell : Encodable.encode cell.1 ≤ cellCode := by
        exact Nat.left_le_pair _ _
      have secondCodeCell : Encodable.encode cell.2 ≤ cellCode := by
        exact Nat.right_le_pair _ _
      have firstCodeLimit : Encodable.encode cell.1 ≤ limit :=
        firstCodeCell.trans cellLimit
      have secondCodeLimit : Encodable.encode cell.2 ≤ limit :=
        secondCodeCell.trans cellLimit
      have firstBits := listCodeEncodeNat_length_mono firstCodeLimit
      have secondBits := listCodeEncodeNat_length_mono secondCodeLimit
      have firstSuccBits := listCodeEncodeNat_length_mono
        (show Encodable.encode cell.1 + 1 ≤ limit by omega)
      have secondSuccBits := listCodeEncodeNat_length_mono
        (show Encodable.encode cell.2 + 1 ≤ limit by omega)
      have unpairLocal := unpairCost_le_linear cellCode
      have unpairArgumentBits := listCodeEncodeNat_length_mono
        (show 2 * cellCode + 4 ≤ limit by
          simp only [limit, packedCenterPolynomialSpaceLimit, motifCode]
          omega)
      have unpairGlobal : unpairCost cellCode ≤
          1000000000 * nativeUnit := by
        simp only [nativeUnit, encodedListSpace_cons,
          encodedListSpace_nil] at unpairLocal ⊢
        omega
      have motifSuffix :
          periodicStrip.motif = leading ++ cell :: remaining := suffix
      have normalizationHead :=
        packedNormalizationHeadCost_le_polynomialSpaceBound
          periodicStrip packed WindowState.center valid cell remaining
          leading motifSuffix
      have normalizationTail :=
        packedNormalizationTailCost_le_polynomialSpaceBound
          periodicStrip packed WindowState.center valid cell remaining
          leading motifSuffix
      have normalizationHeadUnit :
          packedNormalizationHeadCost periodicStrip packed
              WindowState.center valid cell remaining ≤ unit := by
        simp only [unit, packedCenterPolynomialSpaceUnit]
        omega
      have normalizationTailUnit :
          packedNormalizationTailCost periodicStrip packed
              WindowState.center valid cell remaining ≤ unit := by
        simp only [unit, packedCenterPolynomialSpaceUnit]
        omega
      have cellMember : cell ∈ periodicStrip.motif := by
        rw [suffix]
        simp
      have baseLocal := packedCenterBaseValidCost_le_linear
        tromino periodicStrip packed cell
      have baseMaximum := packedCenterBaseValidSpaceBound_le_maximum
        tromino periodicStrip packed cell periodicStrip.motif cellMember
      have baseGlobal :
          packedCenterBaseValidCost tromino periodicStrip packed cell ≤
            unit := by
        simp only [unit, packedCenterPolynomialSpaceUnit]
        omega
      have motifBitsRaw :
          (Computability.encodeNat
            (Encodable.encode periodicStrip.motif)).length ≤
              (Computability.encodeNat limit).length := by
        simpa [motifCode] using motifBits
      have tailBitsRaw :
          (Computability.encodeNat
            (Encodable.encode remaining)).length ≤
              (Computability.encodeNat limit).length := by
        simpa [tailCode] using tailBits
      have nextStateFieldBits :
          (Computability.encodeNat
                (Encodable.encode periodicStrip.motif)).length +
              (Computability.encodeNat
                (Encodable.encode remaining)).length +
              (Computability.encodeNat periodicStrip.period).length +
              (Computability.encodeNat packed.phase).length +
              (Computability.encodeNat WindowState.center.val).length +
              (Computability.encodeNat packed.assignmentWord).length ≤
            6 * (Computability.encodeNat limit).length := by
        clear * - motifBitsRaw tailBitsRaw periodBits phaseBits
          columnBits wordBits
        omega
      have nextStateSpace :
          encodedListSpace
              (Code.packedCenterNativeStep tromino periodicStrip packed
                (Code.packedCenterState periodicStrip packed valid
                  (cell :: remaining))) ≤
            10 * ((Computability.encodeNat limit).length + 2) := by
        rw [Code.packedCenterNativeStep_state_cons]
        cases valid <;>
          cases inside : packed.centerBaseInsideBool
            tromino periodicStrip cell <;>
          cases covered : packed.centerBaseCoveredBool
            tromino periodicStrip cell <;>
          simp [Code.packedCenterState,
            Code.packedNormalizationState,
            encodedListSpace_cons, encodedListSpace_nil,
            motifCode, tailCode, zeroBits, oneBits,
            inside, covered] <;>
          clear * - nextStateFieldBits <;> omega
      cases countdown with
      | zero =>
          cases valid <;>
            simp [packedCenterBodyCost, flatCountdownBodyCost,
              zeroPrimeCost, Code.packedCenterState,
              Code.packedNormalizationState,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, remainingCode, cellCode, tailCode,
              limit, nativeUnit, zeroBits, oneBits, twoBits] at * <;>
            clear * - countdownBits countdownPredBits motifBits
              remainingBits periodBits phaseBits columnBits wordBits
              countdownSuccBits motifSuccBits remainingSuccBits
              periodSuccBits phaseSuccBits columnSuccBits wordSuccBits
              cellBits tailBits constructorBits cellSuccBits
              tailSuccBits firstBits secondBits firstSuccBits
              secondSuccBits nextStateSpace nativeUnitLe <;>
            omega
      | succ countdown =>
          cases valid <;>
            cases inside : packed.centerBaseInsideBool
              tromino periodicStrip cell <;>
            cases covered : packed.centerBaseCoveredBool
              tromino periodicStrip cell <;>
            simp [packedCenterBodyCost, packedCenterStepCost,
              packedCenterConsStepCost, packedCenterUpdatedValidCost,
              packedCenterHeadValidCost, packedCenterBaseArgumentsCost,
              packedCenterHeadRowCost,
              flatCountdownBodyCost, flatCountdownSuccBranchCost,
              branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, boolAndCost, normalizeBoolCost,
              prependCost, getCost, dropCost, idCost, headCost,
              nilCost, oneCost, zeroCost, zeroPrimeCost,
              tailCost, succCost, Code.packedCenterState,
              Code.packedNormalizationState,
              encodedListSpace_cons, encodedListSpace_nil,
              motifCode, remainingCode, cellCode, tailCode,
              limit, nativeUnit, inside, covered,
              zeroBits, oneBits, twoBits] at * <;>
            clear * - countdownBits countdownPredBits motifBits
              remainingBits periodBits phaseBits columnBits wordBits
              countdownSuccBits motifSuccBits remainingSuccBits
              periodSuccBits phaseSuccBits columnSuccBits wordSuccBits
              cellBits tailBits constructorBits cellSuccBits tailSuccBits
              firstBits secondBits firstSuccBits secondSuccBits
              unpairGlobal normalizationHeadUnit normalizationTailUnit
              baseGlobal nextStateSpace nativeUnitLe <;>
            omega

def packedCenterLoopInputCost
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let values := [periodicStrip.period, packed.phase,
    Encodable.encode periodicStrip.motif, packed.assignmentWord]
  let restValid := prependCost values [packed.assignmentWord] [1]
    (getCost 3 values) (oneCost values)
  let restColumn := prependCost values [WindowState.center.val]
    [packed.assignmentWord, 1]
    (numeralCost WindowState.center.val values) restValid
  let restPhase := prependCost values [packed.phase]
    [WindowState.center.val, packed.assignmentWord, 1]
    (getCost 1 values) restColumn
  let restPeriod := prependCost values [periodicStrip.period]
    [packed.phase, WindowState.center.val,
      packed.assignmentWord, 1]
    (getCost 0 values) restPhase
  let restStateMotif := prependCost values
    [Encodable.encode periodicStrip.motif]
    [periodicStrip.period, packed.phase, WindowState.center.val,
      packed.assignmentWord, 1]
    (getCost 2 values) restPeriod
  let restRemaining := prependCost values
    [Encodable.encode periodicStrip.motif]
    [Encodable.encode periodicStrip.motif,
      periodicStrip.period, packed.phase, WindowState.center.val,
      packed.assignmentWord, 1]
    (getCost 2 values) restStateMotif
  prependCost values [Encodable.encode periodicStrip.motif]
    [Encodable.encode periodicStrip.motif,
      Encodable.encode periodicStrip.motif,
      periodicStrip.period, packed.phase, WindowState.center.val,
      packed.assignmentWord, 1]
    (getCost 2 values) restRemaining

theorem packedCenterLoopInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    EvaluatorCodeFits Code.packedCenterLoopInputCode
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      (Encodable.encode periodicStrip.motif ::
        Code.packedCenterState periodicStrip packed
          true periodicStrip.motif)
      (packedCenterLoopInputCost periodicStrip packed) := by
  let values := [periodicStrip.period, packed.phase,
    Encodable.encode periodicStrip.motif, packed.assignmentWord]
  have restValid := prepend (get 3 values) (one values)
  have restColumn := prepend
    (numeral WindowState.center.val values) restValid
  have restPhase := prepend (get 1 values) restColumn
  have restPeriod := prepend (get 0 values) restPhase
  have restStateMotif := prepend (get 2 values) restPeriod
  have restRemaining := prepend (get 2 values) restStateMotif
  have result := prepend (get 2 values) restRemaining
  simpa [Code.packedCenterLoopInputCode,
    packedCenterLoopInputCost, Code.packedCenterState,
    Code.packedNormalizationState, Code.numeral,
    numeralCost, prependCost, values] using result

theorem packedCenterLoopInputCost_le_linear
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterLoopInputCost periodicStrip packed ≤
      10000000000 *
        (encodedListSpace
          [packedCenterPolynomialSpaceLimit periodicStrip packed] + 1) := by
  let values := [periodicStrip.period, packed.phase,
    Encodable.encode periodicStrip.motif, packed.assignmentWord]
  let limit := packedCenterPolynomialSpaceLimit periodicStrip packed
  let unit := encodedListSpace [limit] + 1
  have periodBound : periodicStrip.period ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit]
    omega
  have phaseBound : packed.phase ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit]
    omega
  have motifBound : Encodable.encode periodicStrip.motif ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit]
    omega
  have wordBound : packed.assignmentWord ≤ limit := by
    simp only [limit, packedCenterPolynomialSpaceLimit]
    omega
  have periodBits := listCodeEncodeNat_length_mono periodBound
  have phaseBits := listCodeEncodeNat_length_mono phaseBound
  have motifBits := listCodeEncodeNat_length_mono motifBound
  have wordBits := listCodeEncodeNat_length_mono wordBound
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have oneLimitBits := listCodeEncodeNat_length_mono
    (show 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have positiveLimitBits :
      1 ≤ (Computability.encodeNat limit).length := by
    simpa [oneBits] using oneLimitBits
  have inputSpace : encodedListSpace values ≤ 5 * unit := by
    have raw := encodedListSpace_le_of_fields_le values limit (by
      intro value member
      simp only [values, List.mem_cons] at member
      rcases member with rfl | rfl | rfl | rfl | impossible
      · exact periodBound
      · exact phaseBound
      · exact motifBound
      · exact wordBound
      · simp at impossible)
    simp only [values, List.length_cons, List.length_nil] at raw
    exact raw.trans (by
      simp only [unit, encodedListSpace_cons,
        encodedListSpace_nil]
      omega)
  have get0 := listCodeGetCost_le_linear 0 values
  have get1 := listCodeGetCost_le_linear 1 values
  have get2 := listCodeGetCost_le_linear 2 values
  have get3 := listCodeGetCost_le_linear 3 values
  have zeroBound := listCodeZeroCost_le_linear values
  have addSmall :
      addConstCost WindowState.center.val [0] ≤ 100000 := by
    native_decide
  have centerBits :
      (Computability.encodeNat WindowState.center.val).length ≤ 100 := by
    native_decide
  have numeralBound : numeralCost WindowState.center.val values ≤
      1000000 * unit := by
    simp only [numeralCost]
    omega
  have oneCostBound : oneCost values ≤ 200000 * unit := by
    simp only [oneCost]
    have successorSmall : succCost [0] ≤ 100000 := by
      native_decide
    omega
  change packedCenterLoopInputCost periodicStrip packed ≤
    10000000000 * unit
  dsimp only [unit] at *
  simp [packedCenterLoopInputCost, prependCost, values,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

/-- Maximum exact body cost over every suffix and accumulator value. -/
def packedCenterSuffixSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (countdown : Nat) :
    List Cell -> Nat
  | [] => max
      (packedCenterBodyCost tromino periodicStrip packed
        countdown false [])
      (packedCenterBodyCost tromino periodicStrip packed
        countdown true [])
  | cell :: remaining => max
      (packedCenterBodyCost tromino periodicStrip packed
        countdown false (cell :: remaining))
      (max
        (packedCenterBodyCost tromino periodicStrip packed
          countdown true (cell :: remaining))
        (packedCenterSuffixSpaceBound tromino periodicStrip packed
          countdown remaining))

theorem packedCenterBodyCost_le_suffixSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (countdown : Nat)
    (valid : Bool) (leading remaining : List Cell) :
    packedCenterBodyCost tromino periodicStrip packed
        countdown valid remaining ≤
      packedCenterSuffixSpaceBound tromino periodicStrip packed
        countdown (leading ++ remaining) := by
  induction leading with
  | nil =>
      cases remaining with
      | nil => cases valid <;> simp [packedCenterSuffixSpaceBound]
      | cons cell remaining =>
          cases valid
          · exact Nat.le_max_left _ _
          · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  | cons cell leading induction =>
      have bounded := induction
      simp only [List.cons_append, packedCenterSuffixSpaceBound]
      exact bounded.trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

def packedCenterSpaceBoundUpTo
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat -> Nat
  | 0 => packedCenterSuffixSpaceBound tromino periodicStrip packed
      0 periodicStrip.motif
  | limit + 1 => max
      (packedCenterSuffixSpaceBound tromino periodicStrip packed
        (limit + 1) periodicStrip.motif)
      (packedCenterSpaceBoundUpTo tromino periodicStrip packed limit)

theorem packedCenterSuffixSpaceBound_le_upTo
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown limit : Nat) (bounded : countdown ≤ limit) :
    packedCenterSuffixSpaceBound tromino periodicStrip packed
        countdown periodicStrip.motif ≤
      packedCenterSpaceBoundUpTo tromino periodicStrip packed limit := by
  induction limit with
  | zero =>
      have countdownZero : countdown = 0 := by omega
      subst countdown
      simp [packedCenterSpaceBoundUpTo]
  | succ limit induction =>
      by_cases top : countdown = limit + 1
      · subst countdown
        simp [packedCenterSpaceBoundUpTo]
      · have below : countdown ≤ limit := by omega
        exact (induction below).trans (by
          simp [packedCenterSpaceBoundUpTo])

def packedCenterSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  packedCenterSpaceBoundUpTo tromino periodicStrip packed
    (Encodable.encode periodicStrip.motif)

theorem packedCenterBodyCost_le_spaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown : Nat) (valid : Bool)
    (remaining leading : List Cell)
    (countdownBound : countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedCenterBodyCost tromino periodicStrip packed
        countdown valid remaining ≤
      packedCenterSpaceBound tromino periodicStrip packed := by
  have bodyToSuffix := packedCenterBodyCost_le_suffixSpaceBound
    tromino periodicStrip packed countdown valid leading remaining
  rw [← suffix] at bodyToSuffix
  exact bodyToSuffix.trans
    (packedCenterSuffixSpaceBound_le_upTo tromino periodicStrip packed
      countdown (Encodable.encode periodicStrip.motif) countdownBound)

theorem packedCenterSuffixSpaceBound_le_polynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown : Nat) (remaining leading : List Cell)
    (countdownBound : countdown ≤ Encodable.encode periodicStrip.motif)
    (suffix : periodicStrip.motif = leading ++ remaining) :
    packedCenterSuffixSpaceBound tromino periodicStrip packed
        countdown remaining ≤
      packedCenterPolynomialSpaceBound tromino periodicStrip packed := by
  induction remaining generalizing leading with
  | nil =>
      simp only [packedCenterSuffixSpaceBound]
      apply Nat.max_le.mpr
      constructor
      · exact packedCenterBodyCost_le_polynomialSpaceBound
          tromino periodicStrip packed countdown false [] leading
          countdownBound suffix
      · exact packedCenterBodyCost_le_polynomialSpaceBound
          tromino periodicStrip packed countdown true [] leading
          countdownBound suffix
  | cons cell remaining induction =>
      simp only [packedCenterSuffixSpaceBound]
      apply Nat.max_le.mpr
      constructor
      · exact packedCenterBodyCost_le_polynomialSpaceBound
          tromino periodicStrip packed countdown false
          (cell :: remaining) leading countdownBound suffix
      · apply Nat.max_le.mpr
        constructor
        · exact packedCenterBodyCost_le_polynomialSpaceBound
            tromino periodicStrip packed countdown true
            (cell :: remaining) leading countdownBound suffix
        · apply induction (leading := leading ++ [cell])
          simpa [List.append_assoc] using suffix

theorem packedCenterSpaceBoundUpTo_le_polynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (limit : Nat)
    (limitBound : limit ≤ Encodable.encode periodicStrip.motif) :
    packedCenterSpaceBoundUpTo tromino periodicStrip packed limit ≤
      packedCenterPolynomialSpaceBound tromino periodicStrip packed := by
  induction limit with
  | zero =>
      simpa [packedCenterSpaceBoundUpTo] using
        (packedCenterSuffixSpaceBound_le_polynomialSpaceBound
          tromino periodicStrip packed 0 periodicStrip.motif []
          (Nat.zero_le _) (by simp))
  | succ limit induction =>
      simp only [packedCenterSpaceBoundUpTo]
      apply Nat.max_le.mpr
      constructor
      · exact packedCenterSuffixSpaceBound_le_polynomialSpaceBound
          tromino periodicStrip packed (limit + 1)
          periodicStrip.motif [] limitBound (by simp)
      · exact induction (by omega)

theorem packedCenterSpaceBound_le_polynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterSpaceBound tromino periodicStrip packed ≤
      packedCenterPolynomialSpaceBound tromino periodicStrip packed :=
  packedCenterSpaceBoundUpTo_le_polynomialSpaceBound tromino
    periodicStrip packed (Encodable.encode periodicStrip.motif)
    (Nat.le_refl _)

def PackedCenterReachable
    (_tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown : Nat) (values : List Nat) : Prop :=
  ∃ valid remaining leading,
    values = Code.packedCenterState periodicStrip packed
      valid remaining ∧
    countdown ≤ Encodable.encode periodicStrip.motif ∧
    periodicStrip.motif = leading ++ remaining

theorem packedCenterReachable_initial
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (valid : Bool) :
    PackedCenterReachable tromino periodicStrip packed
      (Encodable.encode periodicStrip.motif)
      (Code.packedCenterState periodicStrip packed
        valid periodicStrip.motif) := by
  exact ⟨valid, periodicStrip.motif, [], rfl,
    Nat.le_refl _, by simp⟩

theorem packedCenterReachable_step
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (countdown : Nat) (values : List Nat)
    (reachable : PackedCenterReachable tromino periodicStrip packed
      (countdown + 1) values) :
    PackedCenterReachable tromino periodicStrip packed countdown
      (Code.packedCenterNativeStep tromino periodicStrip packed values) := by
  obtain ⟨valid, remaining, leading, rfl,
    countdownBound, suffix⟩ := reachable
  cases remaining with
  | nil =>
      exact ⟨valid, [], leading,
        Code.packedCenterNativeStep_state_nil
          tromino periodicStrip packed valid,
        by omega, suffix⟩
  | cons cell remaining =>
      refine ⟨valid &&
          (packed.centerBaseInsideBool tromino periodicStrip cell &&
            packed.centerBaseCoveredBool tromino periodicStrip cell),
        remaining, leading ++ [cell], ?_, by omega, ?_⟩
      · exact Code.packedCenterNativeStep_state_cons
          tromino periodicStrip packed valid cell remaining
      · simpa [List.append_assoc] using suffix

/-- The complete center scan reuses one finite reachable-state envelope. -/
theorem packedCenterFlatUniform
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) :
    EvaluatorCodeFits
      (Code.flatIterate (Code.packedCenterStepCode tromino))
      (Encodable.encode periodicStrip.motif ::
        Code.packedCenterState periodicStrip packed
          true periodicStrip.motif)
      (Code.packedCenterState periodicStrip packed
        (packed.isCenterValidBool tromino periodicStrip) [])
      (packedCenterSpaceBound tromino periodicStrip packed) where
  input_space := by
    have body := packedCenterBody tromino periodicStrip wellFormed packed
      (Encodable.encode periodicStrip.motif) true periodicStrip.motif
    exact body.input_space.trans
      (packedCenterBodyCost_le_spaceBound tromino periodicStrip packed
        (Encodable.encode periodicStrip.motif) true
        periodicStrip.motif [] (Nat.le_refl _) (by simp))
  output_space := by
    let result := packed.isCenterValidBool tromino periodicStrip
    have body := packedCenterBody tromino periodicStrip wellFormed packed
      0 result []
    have input := body.input_space
    have cost := packedCenterBodyCost_le_spaceBound
      tromino periodicStrip packed 0 result [] periodicStrip.motif
      (Nat.zero_le _) (by simp)
    simp only [result] at input cost
    simp only [Code.packedCenterState,
      Code.packedNormalizationState, encodedListSpace_cons] at input ⊢
    omega
  call continuation bound budget after := by
    apply EvaluatorCallFits.flatIterate_of_reachable_code_fits
      (step := Code.packedCenterNativeStep
        tromino periodicStrip packed)
      (bodyCost := fun _ _ =>
        packedCenterSpaceBound tromino periodicStrip packed)
      (invariant := PackedCenterReachable
        tromino periodicStrip packed)
    · intro countdown values reachable
      obtain ⟨valid, remaining, leading, rfl,
        countdownBound, suffix⟩ := reachable
      exact (packedCenterBody tromino periodicStrip wellFormed packed
        countdown valid remaining).mono
        (packedCenterBodyCost_le_spaceBound tromino periodicStrip packed
          countdown valid remaining leading countdownBound suffix)
    · exact packedCenterReachable_initial
        tromino periodicStrip packed true
    · exact packedCenterReachable_step tromino periodicStrip packed
    · intro countdown values reachable
      exact budget
    · rw [Code.packedCenterNativeStep_iterate,
        Code.packedCenterProcess_encode]
      simpa using after

def packedCenterValidCost
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  let result := Code.packedCenterState periodicStrip packed
    (packed.isCenterValidBool tromino periodicStrip) []
  getCost 6 result +
    (packedCenterSpaceBound tromino periodicStrip packed +
      packedCenterLoopInputCost periodicStrip packed)

/-- Fitted closed program for complete packed center validity. -/
theorem packedCenterValid
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) :
    EvaluatorCodeFits (Code.packedCenterValidCode tromino)
      [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        packed.assignmentWord]
      [(packed.isCenterValidBool tromino periodicStrip).toNat]
      (packedCenterValidCost tromino periodicStrip packed) := by
  let result := Code.packedCenterState periodicStrip packed
    (packed.isCenterValidBool tromino periodicStrip) []
  have loop := comp
    (packedCenterFlatUniform tromino periodicStrip wellFormed packed)
    (packedCenterLoopInput periodicStrip packed)
  have projected := comp (get 6 result) loop
  simpa [Code.packedCenterValidCode, packedCenterValidCost,
    result, Code.packedCenterState,
    Code.packedNormalizationState] using projected

def packedCenterValidPolynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) : Nat :=
  100000000000000000000000000000000000000000 *
    (packedCenterPolynomialSpaceUnit tromino periodicStrip packed + 1)

def packedCenterValidPolynomialSpaceBoundLinearCoefficient
    (tromino : Tromino) : Nat :=
  100000000000000000000000000000000000000000 *
    (packedCenterPolynomialSpaceUnitLinearCoefficient tromino + 1)

set_option maxRecDepth 100000 in
theorem packedCenterValidPolynomialSpaceBound_le_input
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterValidPolynomialSpaceBound tromino periodicStrip packed ≤
      packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino *
        packedNormalizationInputUnit periodicStrip packed := by
  let input := packedNormalizationInputUnit periodicStrip packed
  have inputPositive : 1 ≤ input := by
    simp [input, packedNormalizationInputUnit]
  have unit := packedCenterPolynomialSpaceUnit_le_input
    tromino periodicStrip packed
  have plus :
      packedCenterPolynomialSpaceUnit tromino periodicStrip packed + 1 ≤
        (packedCenterPolynomialSpaceUnitLinearCoefficient tromino + 1) *
          input := by
    simp only [input] at unit ⊢
    calc
      _ ≤ packedCenterPolynomialSpaceUnitLinearCoefficient tromino * input +
            1 := Nat.add_le_add_right unit _
      _ ≤ packedCenterPolynomialSpaceUnitLinearCoefficient tromino * input +
            input := Nat.add_le_add_left inputPositive _
      _ = (packedCenterPolynomialSpaceUnitLinearCoefficient tromino + 1) *
            input := by ring
  change
    100000000000000000000000000000000000000000 *
        (packedCenterPolynomialSpaceUnit tromino periodicStrip packed + 1) ≤
      packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino * input
  calc
    _ ≤ 100000000000000000000000000000000000000000 *
          ((packedCenterPolynomialSpaceUnitLinearCoefficient tromino + 1) *
            input) := Nat.mul_le_mul_left _ plus
    _ = _ := by
      rw [packedCenterValidPolynomialSpaceBoundLinearCoefficient]
      exact (Nat.mul_assoc _ _ _).symm

theorem packedCenterValidCost_le_polynomialSpaceBound
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedCenterValidCost tromino periodicStrip packed ≤
      packedCenterValidPolynomialSpaceBound
        tromino periodicStrip packed := by
  let resultBool := packed.isCenterValidBool tromino periodicStrip
  let result := Code.packedCenterState periodicStrip packed resultBool []
  let limit := packedCenterPolynomialSpaceLimit periodicStrip packed
  let nativeUnit := encodedListSpace [limit] + 1
  let unit := packedCenterPolynomialSpaceUnit
    tromino periodicStrip packed
  have nativeUnitLe : nativeUnit ≤ unit := by
    simp only [nativeUnit, unit, packedCenterPolynomialSpaceUnit,
      limit]
    omega
  have motifBits := listCodeEncodeNat_length_mono
    (show Encodable.encode periodicStrip.motif ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have periodBits := listCodeEncodeNat_length_mono
    (show periodicStrip.period ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have phaseBits := listCodeEncodeNat_length_mono
    (show packed.phase ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have columnBits := listCodeEncodeNat_length_mono
    (show WindowState.center.val ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have wordBits := listCodeEncodeNat_length_mono
    (show packed.assignmentWord ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have oneLimitBits := listCodeEncodeNat_length_mono
    (show 1 ≤ limit by
      simp only [limit, packedCenterPolynomialSpaceLimit]
      omega)
  have positiveLimitBits :
      1 ≤ (Computability.encodeNat limit).length := by
    simpa [oneBits] using oneLimitBits
  have resultSpace : encodedListSpace result ≤ 10 * nativeUnit := by
    have nativeUnitEq :
        nativeUnit = (Computability.encodeNat limit).length + 2 := by
      simp [nativeUnit, encodedListSpace_cons, encodedListSpace_nil]
    have boolBits :
        (Computability.encodeNat resultBool.toNat).length ≤
          (Computability.encodeNat limit).length := by
      cases resultBool
      · simp [zeroBits]
      · simpa [oneBits] using positiveLimitBits
    cases resultBool <;>
      simp [result, Code.packedCenterState,
        Code.packedNormalizationState, nativeUnit,
        encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] at * <;> omega
  have getRaw := listCodeGetCost_le_linear 6 result
  have getBound : getCost 6 result ≤ 1000000 * unit := by
    omega
  have bodyBound := packedCenterSpaceBound_le_polynomialSpaceBound
    tromino periodicStrip packed
  have bodyBound' : packedCenterSpaceBound tromino periodicStrip packed ≤
      10000000000000000000000000000000000000000 * unit := by
    simpa [packedCenterPolynomialSpaceBound, unit] using bodyBound
  have inputRaw := packedCenterLoopInputCost_le_linear
    periodicStrip packed
  have inputBound : packedCenterLoopInputCost periodicStrip packed ≤
      10000000000 * unit := by
    exact inputRaw.trans (Nat.mul_le_mul_left _ nativeUnitLe)
  change getCost 6 result +
      (packedCenterSpaceBound tromino periodicStrip packed +
        packedCenterLoopInputCost periodicStrip packed) ≤
    100000000000000000000000000000000000000000 * (unit + 1)
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing

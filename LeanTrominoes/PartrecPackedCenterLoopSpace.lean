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

end EvaluatorCodeFits

end PartrecToTM2
end Turing

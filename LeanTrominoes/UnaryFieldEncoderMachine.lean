/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryCountPaddingMachine

/-!
# Streaming unary fields into canonical native naturals

The compact request printer can emit arbitrary affine atom numbers using one
finite unary marker per unit and a finite field delimiter.  This file defines
the fixed finite machine that turns every such field into the evaluator's
canonical native binary representation.

The verified machine scans every field, increments a canonical binary counter,
drains the counter at each delimiter, and reverses the accumulated native
output.  The final theorem packages the exact execution as a polynomial-time
finite-machine certificate.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryFieldEncoderMachine

inductive Symbol
  | unit
  | delimiter
  deriving DecidableEq, Fintype, Inhabited

inductive Stack
  | source
  | counter
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | increment
  | replaceZero
  | carry
  | restore
  | emitCounter
  | reverseOutput
  deriving Fintype

abbrev State := Option (Symbol ⊕ PartrecToTM2.Γ')

abbrev Alphabet : Stack → Type
  | .source => Symbol
  | .counter | .scratch | .outputReverse | .output => PartrecToTM2.Γ'

def sourceFromState : State → Symbol
  | some (.inl source) => source
  | _ => default

def bitFromState : State → PartrecToTM2.Γ'
  | some (.inr bit) => bit
  | _ => default

def isUnitState : State → Bool
  | some (.inl .unit) => true
  | _ => false

def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .source (fun _ source => source.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.branch isUnitState
            (.load (fun _ => none) (.goto fun _ => .increment))
            (.load (fun _ => none) (.goto fun _ => .emitCounter))))
  | .increment =>
      .pop .counter (fun _ bit => bit.map Sum.inr)
        (.branch Option.isNone
          (.push .scratch (fun _ => .bit1)
            (.goto fun _ => .restore))
          (.goto fun state =>
            if bitFromState state = .bit0 then .replaceZero else .carry))
  | .replaceZero =>
      .push .scratch (fun _ => .bit1)
        (.load (fun _ => none) (.goto fun _ => .restore))
  | .carry =>
      .push .scratch (fun _ => .bit0)
        (.load (fun _ => none) (.goto fun _ => .increment))
  | .restore =>
      .pop .scratch (fun _ bit => bit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .scan)
          (.push .counter bitFromState
            (.load (fun _ => none) (.goto fun _ => .restore))))
  | .emitCounter =>
      .pop .counter (fun _ bit => bit.map Sum.inr)
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .cons)
            (.goto fun _ => .scan))
          (.push .outputReverse bitFromState
            (.load (fun _ => none) (.goto fun _ => .emitCounter))))
  | .reverseOutput =>
      .pop .outputReverse (fun _ bit => bit.map Sum.inr)
        (.branch Option.isNone
          .halt
          (.push .output bitFromState
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := none
  m := program

structure TapeData where
  source : List Symbol
  counter : List PartrecToTM2.Γ'
  scratch : List PartrecToTM2.Γ'
  outputReverse : List PartrecToTM2.Γ'
  output : List PartrecToTM2.Γ'

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .source => data.source
  | .counter => data.counter
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def scanCfg (data : TapeData) := cfg .scan none data
def incrementCfg (data : TapeData) := cfg .increment none data
def replaceZeroCfg (data : TapeData) :=
  cfg .replaceZero (some (.inr .bit0)) data
def carryCfg (bit : PartrecToTM2.Γ') (data : TapeData) :=
  cfg .carry (some (.inr bit)) data
def restoreCfg (data : TapeData) := cfg .restore none data
def emitCounterCfg (data : TapeData) := cfg .emitCounter none data
def reverseOutputCfg (data : TapeData) := cfg .reverseOutput none data

def haltCfg (output : List PartrecToTM2.Γ') :
    TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes ⟨[], [], [], [], output⟩⟩

def haltDataCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes data⟩

@[simp]
theorem update_tapes_source (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.source value =
      tapes { data with source := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_counter
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.counter value =
      tapes { data with counter := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_scratch
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_outputReverse
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scan_nil (data : TapeData) (sourceEq : data.source = []) :
    TM2.step program (scanCfg data) =
      some (reverseOutputCfg { data with source := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, scanCfg, reverseOutputCfg, cfg, tapes]

theorem step_scan_unit (data : TapeData) (sources : List Symbol)
    (sourceEq : data.source = .unit :: sources) :
    TM2.step program (scanCfg data) =
      some (incrementCfg { data with source := sources }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change source = .unit :: sources at sourceEq
  subst source
  simp [TM2.step, program, scanCfg, incrementCfg, cfg, tapes,
    isUnitState]

theorem step_scan_delimiter (data : TapeData) (sources : List Symbol)
    (sourceEq : data.source = .delimiter :: sources) :
    TM2.step program (scanCfg data) =
      some (emitCounterCfg
        { data with source := sources }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change source = .delimiter :: sources at sourceEq
  subst source
  simp [TM2.step, program, scanCfg, emitCounterCfg, cfg, tapes,
    isUnitState]

theorem step_increment_nil (data : TapeData)
    (counterEq : data.counter = []) :
    TM2.step program (incrementCfg data) =
      some (restoreCfg
        { data with counter := [], scratch := .bit1 :: data.scratch }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = [] at counterEq
  subst counter
  simp [TM2.step, program, incrementCfg, restoreCfg, cfg, tapes]

theorem step_increment_bit0 (data : TapeData)
    (tail : List PartrecToTM2.Γ')
    (counterEq : data.counter = .bit0 :: tail) :
    TM2.step program (incrementCfg data) =
      some (replaceZeroCfg { data with counter := tail }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = .bit0 :: tail at counterEq
  subst counter
  simp [TM2.step, program, incrementCfg, replaceZeroCfg, cfg, tapes,
    bitFromState]

theorem step_increment_carry (data : TapeData)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (notZero : bit ≠ .bit0)
    (counterEq : data.counter = bit :: tail) :
    TM2.step program (incrementCfg data) =
      some (carryCfg bit { data with counter := tail }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = bit :: tail at counterEq
  subst counter
  cases bit <;> simp_all [TM2.step, program, incrementCfg, carryCfg,
    cfg, tapes, bitFromState]

theorem step_replaceZero (data : TapeData) :
    TM2.step program (replaceZeroCfg data) =
      some (restoreCfg { data with scratch := .bit1 :: data.scratch }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  simp [TM2.step, program, replaceZeroCfg, restoreCfg, cfg, tapes]

theorem step_carry (bit : PartrecToTM2.Γ') (data : TapeData) :
    TM2.step program (carryCfg bit data) =
      some (incrementCfg { data with scratch := .bit0 :: data.scratch }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  simp [TM2.step, program, carryCfg, incrementCfg, cfg, tapes]

theorem step_restore_nil (data : TapeData)
    (scratchEq : data.scratch = []) :
    TM2.step program (restoreCfg data) =
      some (scanCfg { data with scratch := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreCfg, scanCfg, cfg, tapes]

theorem step_restore_cons (data : TapeData)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (scratchEq : data.scratch = bit :: tail) :
    TM2.step program (restoreCfg data) =
      some (restoreCfg
        { data with
          counter := bit :: data.counter
          scratch := tail }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change scratch = bit :: tail at scratchEq
  subst scratch
  cases bit <;>
    simp [TM2.step, program, restoreCfg, cfg, tapes, bitFromState]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

def zeroSteps {Configuration : Type}
    {transition : Configuration → Option Configuration}
    (configuration : Configuration) :
    EvalsToInTime transition configuration (some configuration) 0 where
  steps := 0
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl 0

/-- Restore a reversed changed low prefix onto the native counter. -/
def restore_evalsInTime (data : TapeData)
    (scratch : List PartrecToTM2.Γ')
    (scratchEq : data.scratch = scratch) :
    EvalsToInTime (TM2.step program) (restoreCfg data)
      (some (scanCfg
        { data with
          counter := scratch.reverse ++ data.counter
          scratch := [] }))
      (scratch.length + 1) := by
  induction scratch generalizing data with
  | nil =>
      have step := oneStep (step_restore_nil data scratchEq)
      convert step using 1 <;> simp
  | cons bit scratch induction =>
      let nextData : TapeData :=
        { data with
          counter := bit :: data.counter
          scratch := scratch }
      have first := oneStep
        (step_restore_cons data bit scratch scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (scratch.length + 1) (restoreCfg data) (restoreCfg nextData)
        (some (scanCfg
          { nextData with
            counter := scratch.reverse ++ nextData.counter
            scratch := [] })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def incrementScannedData (data : TapeData)
    (word : List PartrecToTM2.Γ') : TapeData :=
  { data with
    counter := (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).1
    scratch :=
      (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2 ++
        data.scratch }

def incrementScanTime : List PartrecToTM2.Γ' → Nat
  | [] => 1
  | .bit0 :: _ => 2
  | _ :: word => 2 + incrementScanTime word

/-- Scan the changed low prefix of a canonical increment. -/
def increment_to_restore (data : TapeData)
    (word : List PartrecToTM2.Γ') (counterEq : data.counter = word) :
    EvalsToInTime (TM2.step program) (incrementCfg data)
      (some (restoreCfg (incrementScannedData data word)))
      (incrementScanTime word) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_increment_nil data counterEq)
      convert step using 1 <;>
        simp [incrementScannedData,
          PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
          incrementScanTime]
  | cons bit word induction =>
      cases bit with
      | bit0 =>
          let nextData : TapeData := { data with counter := word }
          have first := oneStep
            (step_increment_bit0 data word counterEq)
          have second := oneStep (step_replaceZero nextData)
          have composed := EvalsToInTime.trans (TM2.step program)
            1 1 (incrementCfg data) (replaceZeroCfg nextData)
            (some (restoreCfg
              { nextData with scratch := .bit1 :: nextData.scratch }))
            first second
          convert composed using 1 <;>
            simp [nextData, incrementScannedData,
              PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
              incrementScanTime]
      | bit1 =>
          let nextData : TapeData :=
            { data with counter := word, scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_increment_carry data .bit1 word (by decide) counterEq)
          have second := oneStep (step_carry .bit1
            { data with counter := word })
          have firstTwo := EvalsToInTime.trans (TM2.step program)
            1 1 (incrementCfg data)
            (carryCfg .bit1 { data with counter := word })
            (some (incrementCfg nextData)) first second
          have rest := induction nextData rfl
          have target : incrementScannedData nextData word =
              incrementScannedData data (.bit1 :: word) := by
            simp [nextData, incrementScannedData,
              PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
              List.append_assoc]
          rw [target] at rest
          have composed := EvalsToInTime.trans (TM2.step program)
            2 (incrementScanTime word) (incrementCfg data)
            (incrementCfg nextData)
            (some (restoreCfg
              (incrementScannedData data (.bit1 :: word))))
            firstTwo rest
          convert composed using 1
          all_goals simp [incrementScanTime]
          all_goals omega
      | cons =>
          let nextData : TapeData :=
            { data with counter := word, scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_increment_carry data .cons word (by decide) counterEq)
          have second := oneStep (step_carry .cons
            { data with counter := word })
          have firstTwo := EvalsToInTime.trans (TM2.step program)
            1 1 (incrementCfg data)
            (carryCfg .cons { data with counter := word })
            (some (incrementCfg nextData)) first second
          have rest := induction nextData rfl
          have target : incrementScannedData nextData word =
              incrementScannedData data (.cons :: word) := by
            simp [nextData, incrementScannedData,
              PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
              List.append_assoc]
          rw [target] at rest
          have composed := EvalsToInTime.trans (TM2.step program)
            2 (incrementScanTime word) (incrementCfg data)
            (incrementCfg nextData)
            (some (restoreCfg
              (incrementScannedData data (.cons :: word))))
            firstTwo rest
          convert composed using 1
          all_goals simp [incrementScanTime]
          all_goals omega
      | consₗ =>
          let nextData : TapeData :=
            { data with counter := word, scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_increment_carry data .consₗ word (by decide) counterEq)
          have second := oneStep (step_carry .consₗ
            { data with counter := word })
          have firstTwo := EvalsToInTime.trans (TM2.step program)
            1 1 (incrementCfg data)
            (carryCfg .consₗ { data with counter := word })
            (some (incrementCfg nextData)) first second
          have rest := induction nextData rfl
          have target : incrementScannedData nextData word =
              incrementScannedData data (.consₗ :: word) := by
            simp [nextData, incrementScannedData,
              PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
              List.append_assoc]
          rw [target] at rest
          have composed := EvalsToInTime.trans (TM2.step program)
            2 (incrementScanTime word) (incrementCfg data)
            (incrementCfg nextData)
            (some (restoreCfg
              (incrementScannedData data (.consₗ :: word))))
            firstTwo rest
          convert composed using 1
          all_goals simp [incrementScanTime]
          all_goals omega

theorem incrementScanTime_le (word : List PartrecToTM2.Γ') :
    incrementScanTime word ≤ 2 * word.length + 2 := by
  induction word with
  | nil => simp [incrementScanTime]
  | cons bit word induction =>
      cases bit <;> simp [incrementScanTime] at * <;> omega

/-- Increment a canonical native natural and return to source scanning. -/
def increment_trNat (data : TapeData) (number : Nat)
    (counterEq : data.counter = PartrecToTM2.trNat number)
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step program) (incrementCfg data)
      (some (scanCfg
        { data with
          counter := PartrecToTM2.trNat number.succ
          scratch := [] }))
      (4 * (PartrecToTM2.trNat number).length + 5) := by
  let word := PartrecToTM2.trNat number
  have scanned := increment_to_restore data word (by
    simpa [word] using counterEq)
  have restored := restore_evalsInTime
    (incrementScannedData data word)
    (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2 (by
      simp [incrementScannedData, scratchEq])
  have finalData :
      { incrementScannedData data word with
        counter :=
          (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry
            word).2.reverse ++
            (incrementScannedData data word).counter
        scratch := [] } =
      { data with
        counter := PartrecToTM2.trNat number.succ
        scratch := [] } := by
    rcases data with ⟨source, counter, scratch, outputReverse, output⟩
    change counter = PartrecToTM2.trNat number at counterEq
    change scratch = [] at scratchEq
    subst counter
    subst scratch
    simp [incrementScannedData,
      PeriodicCNF.TransitionEvaluatorMachine.incrementCarry_spec,
      PeriodicCNF.TransitionEvaluatorMachine.incrementNative_trNat, word]
  rw [finalData] at restored
  have composed := EvalsToInTime.trans (TM2.step program)
    (incrementScanTime word)
    ((PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2.length + 1)
    (incrementCfg data) (restoreCfg (incrementScannedData data word))
    (some (scanCfg
      { data with
        counter := PartrecToTM2.trNat number.succ
        scratch := [] })) scanned restored
  refine
    { toEvalsTo := composed.toEvalsTo
      steps_le_m := composed.steps_le_m.trans ?_ }
  have scanBound := incrementScanTime_le word
  have restoreBound :=
    PeriodicCNF.TransitionEvaluatorMachine.incrementCarry_reverse_length_le word
  dsimp only [word] at scanBound restoreBound ⊢
  omega

theorem step_emitCounter_nil (data : TapeData)
    (counterEq : data.counter = []) :
    TM2.step program (emitCounterCfg data) =
      some (scanCfg
        { data with
          counter := []
          outputReverse := .cons :: data.outputReverse }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = [] at counterEq
  subst counter
  simp [TM2.step, program, emitCounterCfg, scanCfg, cfg, tapes]

theorem step_emitCounter_cons (data : TapeData)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (counterEq : data.counter = bit :: tail) :
    TM2.step program (emitCounterCfg data) =
      some (emitCounterCfg
        { data with
          counter := tail
          outputReverse := bit :: data.outputReverse }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = bit :: tail at counterEq
  subst counter
  cases bit <;>
    simp [TM2.step, program, emitCounterCfg, cfg, tapes, bitFromState]

/-- Drain one canonical counter into the globally reversed output word. -/
def emitCounter_evalsInTime (data : TapeData)
    (word : List PartrecToTM2.Γ') (counterEq : data.counter = word) :
    EvalsToInTime (TM2.step program) (emitCounterCfg data)
      (some (scanCfg
        { data with
          counter := []
          outputReverse :=
            .cons :: word.reverse ++ data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_emitCounter_nil data counterEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData : TapeData :=
        { data with
          counter := word
          outputReverse := bit :: data.outputReverse }
      have first := oneStep
        (step_emitCounter_cons data bit word counterEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1) (emitCounterCfg data)
        (emitCounterCfg nextData)
        (some (scanCfg
          { nextData with
            counter := []
            outputReverse :=
              .cons :: word.reverse ++ nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

theorem step_reverseOutput_nil (data : TapeData)
    (outputReverseEq : data.outputReverse = []) :
    TM2.step program (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons (data : TapeData)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (outputReverseEq : data.outputReverse = bit :: tail) :
    TM2.step program (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := bit :: data.output }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change outputReverse = bit :: tail at outputReverseEq
  subst outputReverse
  cases bit <;>
    simp [TM2.step, program, reverseOutputCfg, cfg, tapes, bitFromState]

def reverseOutput_evalsInTime (data : TapeData)
    (word : List PartrecToTM2.Γ')
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime (TM2.step program) (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_reverseOutput_nil data outputReverseEq)
      convert step using 1 <;> simp
  | cons bit word induction =>
      let nextData : TapeData :=
        { data with
          outputReverse := word
          output := bit :: data.output }
      have first := oneStep
        (step_reverseOutput_cons data bit word outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1) (reverseOutputCfg data)
        (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- One delimiter-terminated unary natural. -/
def unaryField (number : Nat) : List Symbol :=
  List.replicate number .unit ++ [.delimiter]

/-- A complete sequence of delimiter-terminated unary fields. -/
def unaryFields (numbers : List Nat) : List Symbol :=
  numbers.flatMap unaryField

@[simp]
theorem unaryFields_nil : unaryFields [] = [] :=
  rfl

@[simp]
theorem unaryFields_cons (number : Nat) (numbers : List Nat) :
    unaryFields (number :: numbers) =
      unaryField number ++ unaryFields numbers :=
  rfl

theorem trList_cons (number : Nat) (numbers : List Nat) :
    PartrecToTM2.trList (number :: numbers) =
      PartrecToTM2.trNat number ++ [.cons] ++
        PartrecToTM2.trList numbers := by
  simp [PartrecToTM2.trList, List.append_assoc]

def unitScanTime : Nat → Nat → Nat
  | 0, _ => 0
  | units + 1, count =>
      1 + (4 * (PartrecToTM2.trNat count).length + 5) +
        unitScanTime units (count + 1)

/-- Consume a fixed run of unary units, maintaining a canonical native
counter and returning to the scanner before the following delimiter. -/
def units_evalsInTime (units count : Nat) (tail : List Symbol)
    (data : TapeData)
    (sourceEq : data.source = List.replicate units .unit ++ tail)
    (counterEq : data.counter = PartrecToTM2.trNat count)
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step program) (scanCfg data)
      (some (scanCfg
        { data with
          source := tail
          counter := PartrecToTM2.trNat (count + units)
          scratch := [] }))
      (unitScanTime units count) := by
  induction units generalizing count data with
  | zero =>
      rcases data with
        ⟨source, counter, scratch, outputReverse, output⟩
      simp only [List.replicate_zero, List.nil_append] at sourceEq
      change source = tail at sourceEq
      change counter = PartrecToTM2.trNat count at counterEq
      change scratch = [] at scratchEq
      subst source
      subst counter
      subst scratch
      simpa [unitScanTime] using
        (zeroSteps (transition := TM2.step program)
          (scanCfg
            { source := tail
              counter := PartrecToTM2.trNat count
              scratch := []
              outputReverse := outputReverse
              output := output }))
  | succ units induction =>
      rw [List.replicate_succ] at sourceEq
      have first := oneStep
        (step_scan_unit data
          (List.replicate units Symbol.unit ++ tail) sourceEq)
      let nextData : TapeData :=
        { data with
          source := List.replicate units .unit ++ tail }
      have incremented := increment_trNat nextData count (by
        simpa [nextData] using counterEq) (by
          simpa [nextData] using scratchEq)
      let countedData : TapeData :=
        { nextData with
          counter := PartrecToTM2.trNat count.succ
          scratch := [] }
      have firstTwo := EvalsToInTime.trans (TM2.step program)
        1 (4 * (PartrecToTM2.trNat count).length + 5)
        (scanCfg data) (incrementCfg nextData)
        (some (scanCfg countedData)) first (by
          simpa [countedData] using incremented)
      have rest := induction count.succ countedData rfl rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        ((4 * (PartrecToTM2.trNat count).length + 5) + 1)
        (unitScanTime units count.succ)
        (scanCfg data) (scanCfg countedData)
        (some (scanCfg
          { countedData with
            source := tail
            counter := PartrecToTM2.trNat (count.succ + units)
            scratch := [] })) firstTwo rest
      convert composed using 1
      · simp [countedData, nextData]
        congr 3
        omega
      · simp [unitScanTime]
        omega

def fieldTime (number : Nat) : Nat :=
  unitScanTime number 0 + 1 +
    (PartrecToTM2.trNat number).length + 1

/-- Consume and emit one complete delimiter-terminated unary field. -/
def field_evalsInTime (number : Nat) (tail : List Symbol)
    (data : TapeData)
    (sourceEq : data.source = unaryField number ++ tail)
    (counterEq : data.counter = []) (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step program) (scanCfg data)
      (some (scanCfg
        { data with
          source := tail
          counter := []
          scratch := []
          outputReverse :=
            (PartrecToTM2.trNat number ++
              [PartrecToTM2.Γ'.cons]).reverse ++
              data.outputReverse }))
      (fieldTime number) := by
  have units := units_evalsInTime number 0 (.delimiter :: tail) data
    (by simpa [unaryField, List.append_assoc] using sourceEq)
    (by simpa using counterEq) scratchEq
  let countedData : TapeData :=
    { data with
      source := .delimiter :: tail
      counter := PartrecToTM2.trNat number
      scratch := [] }
  have delimiter := oneStep
    (step_scan_delimiter countedData tail rfl)
  let delimitedData : TapeData :=
    { countedData with
      source := tail }
  have emitted := emitCounter_evalsInTime delimitedData
    (PartrecToTM2.trNat number) rfl
  have firstTwo := EvalsToInTime.trans (TM2.step program)
    (unitScanTime number 0) 1 (scanCfg data) (scanCfg countedData)
    (some (emitCounterCfg delimitedData))
    (by simpa [countedData] using units)
    (by simpa [delimitedData] using delimiter)
  have whole := EvalsToInTime.trans (TM2.step program)
    (1 + unitScanTime number 0)
    ((PartrecToTM2.trNat number).length + 1)
    (scanCfg data) (emitCounterCfg delimitedData)
    (some (scanCfg
      { data with
        source := tail
        counter := []
        scratch := []
        outputReverse :=
          (PartrecToTM2.trNat number ++
            [PartrecToTM2.Γ'.cons]).reverse ++
            data.outputReverse })) firstTwo (by
      simpa [delimitedData, countedData, List.reverse_append,
        List.append_assoc] using emitted)
  convert whole using 1
  simp [fieldTime]
  omega

def fieldsTime : List Nat → Nat
  | [] => 1
  | number :: numbers => fieldTime number + fieldsTime numbers

/-- Scan every complete unary field and reach final output reversal with the
reverse of the exact native `trList` word. -/
def fields_evalsInTime (numbers : List Nat) (data : TapeData)
    (sourceEq : data.source = unaryFields numbers)
    (counterEq : data.counter = []) (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step program) (scanCfg data)
      (some (reverseOutputCfg
        { data with
          source := []
          counter := []
          scratch := []
          outputReverse :=
            (PartrecToTM2.trList numbers).reverse ++ data.outputReverse }))
      (fieldsTime numbers) := by
  induction numbers generalizing data with
  | nil =>
      have step := oneStep (step_scan_nil data (by simpa using sourceEq))
      convert step using 1 <;>
        simp [fieldsTime, counterEq, scratchEq]
  | cons number numbers induction =>
      have first := field_evalsInTime number (unaryFields numbers) data
        (by simpa using sourceEq) counterEq scratchEq
      let nextData : TapeData :=
        { data with
          source := unaryFields numbers
          counter := []
          scratch := []
          outputReverse :=
            (PartrecToTM2.trNat number ++
              [PartrecToTM2.Γ'.cons]).reverse ++
              data.outputReverse }
      have rest := induction nextData rfl rfl rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        (fieldTime number) (fieldsTime numbers)
        (scanCfg data) (scanCfg nextData)
        (some (reverseOutputCfg
          { nextData with
            source := []
            counter := []
            scratch := []
            outputReverse :=
              (PartrecToTM2.trList numbers).reverse ++
                nextData.outputReverse })) first rest
      convert composed using 1
      · simp [nextData, List.reverse_append,
          List.append_assoc]
      · simp [fieldsTime]
        omega

theorem initList_eq_scanCfg (symbols : List Symbol) :
    initList machine symbols = scanCfg ⟨symbols, [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List PartrecToTM2.Γ') :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def totalTime (numbers : List Nat) : Nat :=
  fieldsTime numbers + (PartrecToTM2.trList numbers).length + 1

def machine_outputsInTime (numbers : List Nat) :
    TM2OutputsInTime machine (unaryFields numbers)
      (some (PartrecToTM2.trList numbers)) (totalTime numbers) := by
  let initial : TapeData := ⟨unaryFields numbers, [], [], [], []⟩
  let scanned : TapeData :=
    ⟨[], [], [], (PartrecToTM2.trList numbers).reverse, []⟩
  have fieldsRun := fields_evalsInTime numbers initial rfl rfl rfl
  have reverseRun := reverseOutput_evalsInTime scanned
    (PartrecToTM2.trList numbers).reverse rfl
  have whole := EvalsToInTime.trans (TM2.step program)
    (fieldsTime numbers) ((PartrecToTM2.trList numbers).length + 1)
    (scanCfg initial) (reverseOutputCfg scanned)
    (some (haltDataCfg ⟨[], [], [], [], PartrecToTM2.trList numbers⟩))
    (by simpa [initial, scanned] using fieldsRun)
    (by simpa [scanned] using reverseRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step program))^[whole.steps]
        (some (initList machine (unaryFields numbers))) =
          some (haltList machine (PartrecToTM2.trList numbers))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime]
      omega)

@[simp]
theorem unaryField_length (number : Nat) :
    (unaryField number).length = number + 1 := by
  simp [unaryField]

@[simp]
theorem unaryFields_length (numbers : List Nat) :
    (unaryFields numbers).length = numbers.sum + numbers.length := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      simp [unaryFields]
      omega

theorem unitScanTime_le (units count : Nat) :
    unitScanTime units count ≤
      units * (4 * (count + units) + 6) := by
  induction units generalizing count with
  | zero => simp [unitScanTime]
  | succ units induction =>
      rw [unitScanTime]
      have bits := BinaryCountPaddingMachine.trNat_length_le count
      have rest := induction (count + 1)
      nlinarith

theorem trList_length_le_unaryFields_length (numbers : List Nat) :
    (PartrecToTM2.trList numbers).length ≤
      (unaryFields numbers).length := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      rw [trList_cons, unaryFields_cons]
      simp only [List.length_append, List.length_singleton]
      rw [unaryField_length]
      have bits := BinaryCountPaddingMachine.trNat_length_le number
      nlinarith

theorem fieldsTime_le (numbers : List Nat) :
    fieldsTime numbers ≤
      8 * ((unaryFields numbers).length + 1) ^ 2 := by
  induction numbers with
  | nil => simp [fieldsTime]
  | cons number numbers induction =>
      rw [fieldsTime]
      unfold fieldTime
      have units := unitScanTime_le number 0
      have bits := BinaryCountPaddingMachine.trNat_length_le number
      rw [unaryFields_cons, List.length_append, unaryField_length]
      have numberNonnegative : 0 ≤ number := Nat.zero_le _
      have restNonnegative : 0 ≤ (unaryFields numbers).length :=
        Nat.zero_le _
      nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 10 * (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le (numbers : List Nat) :
    totalTime numbers ≤
      timePolynomial.eval (unaryFields numbers).length := by
  rw [timePolynomial_eval]
  have fieldsBound := fieldsTime_le numbers
  have outputBound := trList_length_le_unaryFields_length numbers
  unfold totalTime
  nlinarith

/-- Encoding a sequence of delimiter-terminated unary fields as canonical
native naturals is polynomial-time. -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Nat) (List Nat) Symbol PartrecToTM2.Γ'
      unaryFields PartrecToTM2.trList id where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun numbers := by
    have run := machine_outputsInTime numbers
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Symbol).invFun (unaryFields numbers))
        (some (List.map (Equiv.refl PartrecToTM2.Γ').invFun
          (PartrecToTM2.trList (id numbers))))
        (totalTime numbers) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (totalTime_le numbers) }

end UnaryFieldEncoderMachine
end LeanTrominoes

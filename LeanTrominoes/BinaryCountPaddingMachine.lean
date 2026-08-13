/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionEvaluatorMachine
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Binary selected-symbol count padding

This finite machine preserves an input word and appends the canonical native
little-endian binary encoding of the number of selected input symbols.  It is
the bridge between unary loop blocks and the native natural fields consumed
by the periodic-CNF request printer.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BinaryCountPaddingMachine

inductive Stack
  | source
  | counter
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | select
  | increment
  | replaceZero
  | carry
  | restore
  | emitCounter
  | reverseOutput
  deriving Fintype

abbrev State (Source : Type) := Option (Source ⊕ PartrecToTM2.Γ')

abbrev Alphabet (Source : Type) : Stack → Type
  | .source => Source
  | .counter | .scratch => PartrecToTM2.Γ'
  | .outputReverse | .output => Source ⊕ PartrecToTM2.Γ'

def sourceFromState {Source : Type} [Inhabited Source] :
    State Source → Source
  | some (.inl source) => source
  | _ => default

def bitFromState {Source : Type} :
    State Source → PartrecToTM2.Γ'
  | some (.inr bit) => bit
  | _ => default

def program {Source : Type} [Inhabited Source]
    (selected : Source → Bool) :
    Label → TM2.Stmt (Alphabet Source) Label (State Source)
  | .scan =>
      .pop .source (fun _ source => source.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .emitCounter)
          (.push .outputReverse (fun state => .inl (sourceFromState state))
            (.goto fun _ => .select)))
  | .select =>
      .branch (fun state => selected (sourceFromState state))
        (.load (fun _ => none) (.goto fun _ => .increment))
        (.load (fun _ => none) (.goto fun _ => .scan))
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
          (.push .counter (fun state => bitFromState state)
            (.load (fun _ => none) (.goto fun _ => .restore))))
  | .emitCounter =>
      .pop .counter (fun _ bit => bit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.push .outputReverse (fun state => .inr (bitFromState state))
            (.load (fun _ => none) (.goto fun _ => .emitCounter))))
  | .reverseOutput =>
      .pop .outputReverse (fun _ symbol => symbol)
        (.branch Option.isNone
          .halt
          (.push .output (fun state => state.getD (Sum.inr default))
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))

abbrev machine (Source : Type) [Fintype Source] [Inhabited Source]
    (selected : Source → Bool) : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .output
  Γ := Alphabet Source
  Λ := Label
  main := .scan
  σ := State Source
  initialState := none
  m := program selected

structure TapeData (Source : Type) where
  source : List Source
  counter : List PartrecToTM2.Γ'
  scratch : List PartrecToTM2.Γ'
  outputReverse : List (Source ⊕ PartrecToTM2.Γ')
  output : List (Source ⊕ PartrecToTM2.Γ')

def tapes {Source : Type} (data : TapeData Source) :
    ∀ stack, List (Alphabet Source stack)
  | .source => data.source
  | .counter => data.counter
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg {Source : Type} (label : Label) (state : State Source)
    (data : TapeData Source) :
    TM2.Cfg (Alphabet Source) Label (State Source) :=
  ⟨some label, state, tapes data⟩

def scanCfg {Source : Type} (data : TapeData Source) :=
  cfg .scan none data

def selectCfg {Source : Type} (source : Source) (data : TapeData Source) :=
  cfg .select (some (.inl source)) data

def incrementCfg {Source : Type} (data : TapeData Source) :=
  cfg .increment none data

def replaceZeroCfg {Source : Type} (data : TapeData Source) :=
  cfg .replaceZero (some (.inr .bit0)) data

def carryCfg {Source : Type} (bit : PartrecToTM2.Γ')
    (data : TapeData Source) :=
  cfg .carry (some (.inr bit)) data

def restoreCfg {Source : Type} (data : TapeData Source) :=
  cfg .restore none data

def emitCounterCfg {Source : Type} (data : TapeData Source) :=
  cfg .emitCounter none data

def reverseOutputCfg {Source : Type} (data : TapeData Source) :=
  cfg .reverseOutput none data

def haltCfg {Source : Type} (output : List (Source ⊕ PartrecToTM2.Γ')) :
    TM2.Cfg (Alphabet Source) Label (State Source) :=
  ⟨none, none, tapes ⟨[], [], [], [], output⟩⟩

def haltDataCfg {Source : Type} (data : TapeData Source) :
    TM2.Cfg (Alphabet Source) Label (State Source) :=
  ⟨none, none, tapes data⟩

@[simp]
theorem haltDataCfg_empty_eq_haltCfg {Source : Type}
    (output : List (Source ⊕ PartrecToTM2.Γ')) :
    haltDataCfg ⟨[], [], [], [], output⟩ = haltCfg output := rfl

theorem initList_eq_scanCfg {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (sources : List Source) :
    initList (machine Source selected) sources =
      scanCfg ⟨sources, [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool)
    (output : List (Source ⊕ PartrecToTM2.Γ')) :
    haltList (machine Source selected) output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp]
theorem update_tapes_source {Source : Type} (data : TapeData Source)
    (value : List Source) :
    Function.update (tapes data) Stack.source value =
      tapes { data with source := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_counter {Source : Type} (data : TapeData Source)
    (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.counter value =
      tapes { data with counter := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_scratch {Source : Type} (data : TapeData Source)
    (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_outputReverse {Source : Type} (data : TapeData Source)
    (value : List (Source ⊕ PartrecToTM2.Γ')) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output {Source : Type} (data : TapeData Source)
    (value : List (Source ⊕ PartrecToTM2.Γ')) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scan_nil {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (sourceEq : data.source = []) :
    TM2.step (program selected) (scanCfg data) =
      some (emitCounterCfg { data with source := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, scanCfg, emitCounterCfg, cfg, tapes,
    Function.update]

theorem step_scan_cons {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (source : Source) (sources : List Source)
    (sourceEq : data.source = source :: sources) :
    TM2.step (program selected) (scanCfg data) =
      some (selectCfg source
        { data with
          source := sources
          outputReverse := .inl source :: data.outputReverse }) := by
  rcases data with ⟨input, counter, scratch, outputReverse, output⟩
  change input = source :: sources at sourceEq
  subst input
  simp [TM2.step, program, scanCfg, selectCfg, cfg, tapes,
    sourceFromState, Function.update]

theorem step_select_true {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (source : Source) (data : TapeData Source)
    (choice : selected source = true) :
    TM2.step (program selected) (selectCfg source data) =
      some (incrementCfg data) := by
  simp [TM2.step, program, selectCfg, incrementCfg, cfg,
    sourceFromState, choice]

theorem step_select_false {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (source : Source) (data : TapeData Source)
    (choice : selected source = false) :
    TM2.step (program selected) (selectCfg source data) =
      some (scanCfg data) := by
  simp [TM2.step, program, selectCfg, scanCfg, cfg,
    sourceFromState, choice]

theorem step_increment_nil {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (counterEq : data.counter = []) :
    TM2.step (program selected) (incrementCfg data) =
      some (restoreCfg
        { data with counter := [], scratch := .bit1 :: data.scratch }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = [] at counterEq
  subst counter
  simp [TM2.step, program, incrementCfg, restoreCfg, cfg, tapes,
    Function.update]

theorem step_increment_bit0 {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (tail : List PartrecToTM2.Γ')
    (counterEq : data.counter = .bit0 :: tail) :
    TM2.step (program selected) (incrementCfg data) =
      some (replaceZeroCfg { data with counter := tail }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = .bit0 :: tail at counterEq
  subst counter
  simp [TM2.step, program, incrementCfg, replaceZeroCfg, cfg, tapes,
    bitFromState, Function.update]

theorem step_increment_carry {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (notZero : bit ≠ .bit0)
    (counterEq : data.counter = bit :: tail) :
    TM2.step (program selected) (incrementCfg data) =
      some (carryCfg bit { data with counter := tail }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = bit :: tail at counterEq
  subst counter
  cases bit <;> simp_all [TM2.step, program, incrementCfg, carryCfg,
    cfg, tapes, bitFromState, Function.update]

theorem step_replaceZero {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source) :
    TM2.step (program selected) (replaceZeroCfg data) =
      some (restoreCfg { data with scratch := .bit1 :: data.scratch }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  simp [TM2.step, program, replaceZeroCfg, restoreCfg, cfg, tapes,
    Function.update]

theorem step_carry {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (bit : PartrecToTM2.Γ')
    (data : TapeData Source) :
    TM2.step (program selected) (carryCfg bit data) =
      some (incrementCfg { data with scratch := .bit0 :: data.scratch }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  simp [TM2.step, program, carryCfg, incrementCfg, cfg, tapes,
    Function.update]

theorem step_restore_nil {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (scratchEq : data.scratch = []) :
    TM2.step (program selected) (restoreCfg data) =
      some (scanCfg { data with scratch := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreCfg, scanCfg, cfg, tapes,
    Function.update]

theorem step_restore_cons {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (scratchEq : data.scratch = bit :: tail) :
    TM2.step (program selected) (restoreCfg data) =
      some (restoreCfg
        { data with
          counter := bit :: data.counter
          scratch := tail }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change scratch = bit :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreCfg, cfg, tapes, bitFromState,
    Function.update]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

/-- Restore a reversed changed low prefix onto the native counter. -/
def restore_evalsInTime {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (scratch : List PartrecToTM2.Γ')
    (scratchEq : data.scratch = scratch) :
    EvalsToInTime (TM2.step (program selected))
      (restoreCfg data)
      (some (scanCfg
        { data with
          counter := scratch.reverse ++ data.counter
          scratch := [] }))
      (scratch.length + 1) := by
  induction scratch generalizing data with
  | nil =>
      have step := oneStep (step_restore_nil selected data scratchEq)
      convert step using 1 <;> simp [scratchEq]
  | cons bit scratch induction =>
      let nextData : TapeData Source :=
        { data with
          counter := bit :: data.counter
          scratch := scratch }
      have first := oneStep
        (step_restore_cons selected data bit scratch scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program selected))
        1 (scratch.length + 1)
        (restoreCfg data) (restoreCfg nextData)
        (some (scanCfg
          { nextData with
            counter := scratch.reverse ++ nextData.counter
            scratch := [] }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Two-label carry-scan cost. -/
def incrementScanTime : List PartrecToTM2.Γ' → Nat
  | [] => 1
  | .bit0 :: _ => 2
  | _ :: rest => incrementScanTime rest + 2

def incrementScannedData {Source : Type} (data : TapeData Source)
    (word : List PartrecToTM2.Γ') : TapeData Source :=
  { data with
    counter := (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).1
    scratch :=
      (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2 ++
        data.scratch }

/-- The carry scan reaches restoration with exactly the native increment's
high suffix and changed low prefix. -/
def increment_to_restore {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (word : List PartrecToTM2.Γ') (counterEq : data.counter = word) :
    EvalsToInTime (TM2.step (program selected))
      (incrementCfg data)
      (some (restoreCfg (incrementScannedData data word)))
      (incrementScanTime word) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_increment_nil selected data counterEq)
      convert step using 1 <;>
        simp [incrementScannedData,
          PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
          incrementScanTime,
          counterEq]
  | cons bit word induction =>
      cases bit with
      | bit0 =>
          let nextData : TapeData Source := { data with counter := word }
          have first := oneStep
            (step_increment_bit0 selected data word counterEq)
          have second := oneStep (step_replaceZero selected nextData)
          have composed := EvalsToInTime.trans (TM2.step (program selected))
            1 1 (incrementCfg data) (replaceZeroCfg nextData)
            (some (restoreCfg
              { nextData with scratch := .bit1 :: nextData.scratch }))
            first second
          convert composed using 1 <;>
            simp [nextData, incrementScannedData,
              PeriodicCNF.TransitionEvaluatorMachine.incrementCarry,
              incrementScanTime, counterEq]
      | bit1 =>
          let nextData : TapeData Source :=
            { data with counter := word, scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_increment_carry selected data .bit1 word (by decide)
              counterEq)
          have second := oneStep (step_carry selected .bit1
            { data with counter := word })
          have firstTwo := EvalsToInTime.trans (TM2.step (program selected))
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
          have composed := EvalsToInTime.trans (TM2.step (program selected))
            2 (incrementScanTime word)
            (incrementCfg data) (incrementCfg nextData)
            (some (restoreCfg
              (incrementScannedData data (.bit1 :: word))))
            firstTwo rest
          convert composed using 1 <;> simp [incrementScanTime]
      | cons =>
          let nextData : TapeData Source :=
            { data with counter := word, scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_increment_carry selected data .cons word (by decide)
              counterEq)
          have second := oneStep (step_carry selected .cons
            { data with counter := word })
          have firstTwo := EvalsToInTime.trans (TM2.step (program selected))
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
          have composed := EvalsToInTime.trans (TM2.step (program selected))
            2 (incrementScanTime word)
            (incrementCfg data) (incrementCfg nextData)
            (some (restoreCfg
              (incrementScannedData data (.cons :: word))))
            firstTwo rest
          convert composed using 1 <;> simp [incrementScanTime]
      | consₗ =>
          let nextData : TapeData Source :=
            { data with counter := word, scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_increment_carry selected data .consₗ word (by decide)
              counterEq)
          have second := oneStep (step_carry selected .consₗ
            { data with counter := word })
          have firstTwo := EvalsToInTime.trans (TM2.step (program selected))
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
          have composed := EvalsToInTime.trans (TM2.step (program selected))
            2 (incrementScanTime word)
            (incrementCfg data) (incrementCfg nextData)
            (some (restoreCfg
              (incrementScannedData data (.consₗ :: word))))
            firstTwo rest
          convert composed using 1 <;> simp [incrementScanTime]

theorem incrementScanTime_le (word : List PartrecToTM2.Γ') :
    incrementScanTime word ≤ 2 * word.length + 2 := by
  induction word with
  | nil => simp [incrementScanTime]
  | cons bit word induction =>
      cases bit <;> simp [incrementScanTime] at * <;> omega

/-- Increment a canonical native natural and return to source scanning. -/
def increment_trNat {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source) (number : Nat)
    (counterEq : data.counter = PartrecToTM2.trNat number)
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program selected))
      (incrementCfg data)
      (some (scanCfg
        { data with
          counter := PartrecToTM2.trNat number.succ
          scratch := [] }))
      (4 * (PartrecToTM2.trNat number).length + 5) := by
  let word := PartrecToTM2.trNat number
  have scanned := increment_to_restore selected data word (by
    simpa [word] using counterEq)
  have restored := restore_evalsInTime selected
    (incrementScannedData data word)
    (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2 (by
      simp [incrementScannedData, scratchEq])
  have finalData :
      { incrementScannedData data word with
        counter :=
          (PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2.reverse ++
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
  have composed := EvalsToInTime.trans (TM2.step (program selected))
    (incrementScanTime word)
    ((PeriodicCNF.TransitionEvaluatorMachine.incrementCarry word).2.length + 1)
    (incrementCfg data)
    (restoreCfg (incrementScannedData data word))
    (some (scanCfg
      { data with
        counter := PartrecToTM2.trNat number.succ
        scratch := [] }))
    scanned restored
  refine
    { toEvalsTo := composed.toEvalsTo
      steps_le_m := composed.steps_le_m.trans ?_ }
  have scanBound := incrementScanTime_le word
  have restoreBound :=
    PeriodicCNF.TransitionEvaluatorMachine.incrementCarry_reverse_length_le word
  dsimp only [word] at scanBound restoreBound ⊢
  omega

theorem step_emitCounter_nil {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (counterEq : data.counter = []) :
    TM2.step (program selected) (emitCounterCfg data) =
      some (reverseOutputCfg { data with counter := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = [] at counterEq
  subst counter
  simp [TM2.step, program, emitCounterCfg, reverseOutputCfg, cfg,
    tapes, Function.update]

theorem step_emitCounter_cons {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (bit : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (counterEq : data.counter = bit :: tail) :
    TM2.step (program selected) (emitCounterCfg data) =
      some (emitCounterCfg
        { data with
          counter := tail
          outputReverse := .inr bit :: data.outputReverse }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change counter = bit :: tail at counterEq
  subst counter
  cases bit <;>
    simp [TM2.step, program, emitCounterCfg, cfg, tapes, bitFromState,
      Function.update]

def emitCounter_evalsInTime {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (word : List PartrecToTM2.Γ') (counterEq : data.counter = word) :
    EvalsToInTime (TM2.step (program selected))
      (emitCounterCfg data)
      (some (reverseOutputCfg
        { data with
          counter := []
          outputReverse :=
            (word.map fun bit =>
              (Sum.inr bit : Source ⊕ PartrecToTM2.Γ')).reverse ++
            data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_emitCounter_nil selected data counterEq)
      convert step using 1 <;> simp [counterEq]
  | cons bit word induction =>
      let nextData : TapeData Source :=
        { data with
          counter := word
          outputReverse := .inr bit :: data.outputReverse }
      have first := oneStep
        (step_emitCounter_cons selected data bit word counterEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program selected))
        1 (word.length + 1)
        (emitCounterCfg data) (emitCounterCfg nextData)
        (some (reverseOutputCfg
          { nextData with
            counter := []
            outputReverse :=
              (word.map fun bit =>
                (Sum.inr bit : Source ⊕ PartrecToTM2.Γ')).reverse ++
              nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

theorem step_reverseOutput_nil {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (outputReverseEq : data.outputReverse = []) :
    TM2.step (program selected) (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes,
    Function.update]

theorem step_reverseOutput_cons {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (symbol : Source ⊕ PartrecToTM2.Γ')
    (tail : List (Source ⊕ PartrecToTM2.Γ'))
    (outputReverseEq : data.outputReverse = symbol :: tail) :
    TM2.step (program selected) (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := symbol :: data.output }) := by
  rcases data with ⟨source, counter, scratch, outputReverse, output⟩
  change outputReverse = symbol :: tail at outputReverseEq
  subst outputReverse
  cases symbol with
  | inl sourceSymbol =>
      simp [TM2.step, program, reverseOutputCfg, cfg, tapes,
        Function.update]
  | inr bit =>
      cases bit <;>
        simp [TM2.step, program, reverseOutputCfg, cfg, tapes,
          Function.update]

def reverseOutput_evalsInTime {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (data : TapeData Source)
    (outputReverse : List (Source ⊕ PartrecToTM2.Γ'))
    (outputReverseEq : data.outputReverse = outputReverse) :
    EvalsToInTime (TM2.step (program selected))
      (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := outputReverse.reverse ++ data.output }))
      (outputReverse.length + 1) := by
  induction outputReverse generalizing data with
  | nil =>
      have step := oneStep (step_reverseOutput_nil selected data
        outputReverseEq)
      convert step using 1 <;> simp [outputReverseEq]
  | cons symbol outputReverse induction =>
      let nextData : TapeData Source :=
        { data with
          outputReverse := outputReverse
          output := symbol :: data.output }
      have first := oneStep
        (step_reverseOutput_cons selected data symbol outputReverse
          outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step (program selected))
        1 (outputReverse.length + 1)
        (reverseOutputCfg data) (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := outputReverse.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Number of selected symbols in the retained source word. -/
def selectedCount {Source : Type} (selected : Source → Bool) :
    List Source → Nat
  | [] => 0
  | source :: sources =>
      (if selected source then 1 else 0) + selectedCount selected sources

@[simp]
theorem selectedCount_cons {Source : Type} (selected : Source → Bool)
    (source : Source) (sources : List Source) :
    selectedCount selected (source :: sources) =
      (if selected source then 1 else 0) +
        selectedCount selected sources := rfl

def scanTime {Source : Type} (selected : Source → Bool) :
    List Source → Nat → Nat
  | [], _ => 1
  | source :: sources, count =>
      2 +
        (if selected source then
          4 * (PartrecToTM2.trNat count).length + 5
        else 0) +
        scanTime selected sources
          (count + if selected source then 1 else 0)

/-- Scan and preserve every source symbol while incrementing the native
counter once per selected symbol. -/
def scan_evalsInTime {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (sources : List Source) (count : Nat)
    (outputReverse : List (Source ⊕ PartrecToTM2.Γ')) :
    EvalsToInTime (TM2.step (program selected))
      (scanCfg
        ⟨sources, PartrecToTM2.trNat count, [], outputReverse, []⟩)
      (some (emitCounterCfg
        ⟨[],
          PartrecToTM2.trNat (count + selectedCount selected sources),
          [],
          (sources.map fun source =>
            (Sum.inl source : Source ⊕ PartrecToTM2.Γ')).reverse ++
              outputReverse,
          []⟩))
      (scanTime selected sources count) := by
  induction sources generalizing count outputReverse with
  | nil =>
      have step := oneStep (step_scan_nil selected
        ⟨[], PartrecToTM2.trNat count, [], outputReverse, []⟩ rfl)
      convert step using 1 <;> simp [scanTime, selectedCount]
  | cons source sources induction =>
      let afterScan : TapeData Source :=
        ⟨sources, PartrecToTM2.trNat count, [],
          .inl source :: outputReverse, []⟩
      have first := oneStep (step_scan_cons selected
        ⟨source :: sources, PartrecToTM2.trNat count, [],
          outputReverse, []⟩ source sources rfl)
      by_cases choice : selected source = true
      · have second := oneStep
          (step_select_true selected source afterScan choice)
        have increment := increment_trNat selected afterScan count rfl rfl
        have prefixRun := EvalsToInTime.trans (TM2.step (program selected))
          1 1
          (scanCfg
            ⟨source :: sources, PartrecToTM2.trNat count, [],
              outputReverse, []⟩)
          (selectCfg source afterScan) (some (incrementCfg afterScan))
          first second
        have throughIncrement := EvalsToInTime.trans
          (TM2.step (program selected)) 2
          (4 * (PartrecToTM2.trNat count).length + 5)
          (scanCfg
            ⟨source :: sources, PartrecToTM2.trNat count, [],
              outputReverse, []⟩)
          (incrementCfg afterScan)
          (some (scanCfg
            { afterScan with
              counter := PartrecToTM2.trNat count.succ
              scratch := [] }))
          prefixRun increment
        have rest := induction (count + 1) (.inl source :: outputReverse)
        have whole := EvalsToInTime.trans (TM2.step (program selected))
          (2 + (4 * (PartrecToTM2.trNat count).length + 5))
          (scanTime selected sources (count + 1))
          (scanCfg
            ⟨source :: sources, PartrecToTM2.trNat count, [],
              outputReverse, []⟩)
          (scanCfg
            ⟨sources, PartrecToTM2.trNat (count + 1), [],
              .inl source :: outputReverse, []⟩)
          (some (emitCounterCfg
            ⟨[],
              PartrecToTM2.trNat
                ((count + 1) + selectedCount selected sources),
              [],
              (sources.map fun source =>
                (Sum.inl source : Source ⊕ PartrecToTM2.Γ')).reverse ++
                .inl source :: outputReverse, []⟩))
          (by
            convert throughIncrement using 1 <;>
              simp [afterScan, Nat.succ_eq_add_one] <;> omega)
          rest
        convert whole using 1
        · simp [selectedCount, choice, List.reverse_cons,
            List.append_assoc]
          congr 3
          omega
        · simp [scanTime, choice]
          omega
      · have choiceFalse : selected source = false := by
          exact Bool.eq_false_of_not_eq_true choice
        have second := oneStep
          (step_select_false selected source afterScan choiceFalse)
        have prefixRun := EvalsToInTime.trans (TM2.step (program selected))
          1 1
          (scanCfg
            ⟨source :: sources, PartrecToTM2.trNat count, [],
              outputReverse, []⟩)
          (selectCfg source afterScan) (some (scanCfg afterScan)) first second
        have rest := induction count (.inl source :: outputReverse)
        have whole := EvalsToInTime.trans (TM2.step (program selected))
          2 (scanTime selected sources count)
          (scanCfg
            ⟨source :: sources, PartrecToTM2.trNat count, [],
              outputReverse, []⟩)
          (scanCfg afterScan)
          (some (emitCounterCfg
            ⟨[], PartrecToTM2.trNat
                (count + selectedCount selected sources),
              [],
              (sources.map fun source =>
                (Sum.inl source : Source ⊕ PartrecToTM2.Γ')).reverse ++
                .inl source :: outputReverse, []⟩))
          prefixRun rest
        convert whole using 1
        · simp [selectedCount, choiceFalse, List.reverse_cons,
            List.append_assoc]
        · simp [scanTime, choiceFalse]
          omega

theorem selectedCount_le_length {Source : Type}
    (selected : Source → Bool) (sources : List Source) :
    selectedCount selected sources ≤ sources.length := by
  induction sources with
  | nil => rfl
  | cons source sources induction =>
      by_cases choice : selected source = true <;>
        simp [selectedCount, choice] at * <;> omega

theorem trNat_length_le (number : Nat) :
    (PartrecToTM2.trNat number).length ≤ number := by
  rw [Complexity.partrec_trNat_length]
  exact PartrecToTM2.encodeNat_length_le_self number

theorem scanTime_le {Source : Type} (selected : Source → Bool)
    (sources : List Source) (count : Nat) :
    scanTime selected sources count ≤
      2 * sources.length +
        sources.length * (4 * (count + sources.length) + 5) + 1 := by
  induction sources generalizing count with
  | nil => simp [scanTime]
  | cons source sources induction =>
      by_cases choice : selected source = true
      · rw [scanTime]
        simp only [choice, if_true, List.length_cons]
        have rest := induction (count + 1)
        have bits := trNat_length_le count
        nlinarith
      · have choiceFalse : selected source = false :=
          Bool.eq_false_of_not_eq_true choice
        rw [scanTime]
        simp [choiceFalse]
        have rest := induction count
        nlinarith

/-- Semantic output: the retained source followed by one undelimited native
binary counter.  Constructor tags make the two blocks unambiguous, including
the empty encoding of zero. -/
def paddedOutput {Source : Type} (selected : Source → Bool)
    (sources : List Source) : List (Source ⊕ PartrecToTM2.Γ') :=
  sources.map (fun source =>
      (Sum.inl source : Source ⊕ PartrecToTM2.Γ')) ++
    (PartrecToTM2.trNat (selectedCount selected sources)).map (fun bit =>
      (Sum.inr bit : Source ⊕ PartrecToTM2.Γ'))

def totalTime {Source : Type} (selected : Source → Bool)
    (sources : List Source) : Nat :=
  scanTime selected sources 0 +
    (PartrecToTM2.trNat (selectedCount selected sources)).length + 1 +
    (sources.length +
      (PartrecToTM2.trNat (selectedCount selected sources)).length) + 1

def machine_outputsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (sources : List Source) :
    TM2OutputsInTime (machine Source selected) sources
      (some (paddedOutput selected sources))
      (totalTime selected sources) := by
  let count := selectedCount selected sources
  let sourceReverse : List (Source ⊕ PartrecToTM2.Γ') :=
    (sources.map fun source => Sum.inl source).reverse
  let counter := PartrecToTM2.trNat count
  let counterReverse : List (Source ⊕ PartrecToTM2.Γ') :=
    (counter.map fun bit => Sum.inr bit).reverse
  have scanned := scan_evalsInTime selected sources 0 []
  have emitted := emitCounter_evalsInTime selected
    (Source := Source) ⟨[], counter, [], sourceReverse, []⟩ counter rfl
  have reversed := reverseOutput_evalsInTime selected
    (Source := Source)
    ⟨[], [], [], counterReverse ++ sourceReverse, []⟩
    (counterReverse ++ sourceReverse) rfl
  have firstTwo := EvalsToInTime.trans (TM2.step (program selected))
    (scanTime selected sources 0) (counter.length + 1)
    (scanCfg ⟨sources, [], [], [], []⟩)
    (emitCounterCfg ⟨[], counter, [], sourceReverse, []⟩)
    (some (reverseOutputCfg
      ⟨[], [], [], counterReverse ++ sourceReverse, []⟩))
    (by simpa [count, counter, sourceReverse] using scanned)
    (by simpa [counter, counterReverse, sourceReverse] using emitted)
  have whole := EvalsToInTime.trans (TM2.step (program selected))
    ((counter.length + 1) + scanTime selected sources 0)
    ((counterReverse ++ sourceReverse).length + 1)
    (scanCfg ⟨sources, [], [], [], []⟩)
    (reverseOutputCfg
      ⟨[], [], [], counterReverse ++ sourceReverse, []⟩)
    (some (haltDataCfg
      ⟨[], [], [], [],
        (counterReverse ++ sourceReverse).reverse⟩))
    firstTwo (by simpa using reversed)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step (program selected)))^[whole.steps]
      (some (initList (machine Source selected) sources)) =
        some (haltList (machine Source selected)
          (paddedOutput selected sources))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rw [haltDataCfg_empty_eq_haltCfg]
    congr 2
    simp [paddedOutput, count, counter, sourceReverse, counterReverse,
      List.reverse_append]
  · have bound := whole.steps_le_m
    simp [totalTime, count, counter, counterReverse, sourceReverse] at bound ⊢
    omega

theorem totalTime_le (Source : Type) [Fintype Source] [Inhabited Source]
    (selected : Source → Bool) (sources : List Source) :
    totalTime selected sources ≤ 5 * (sources.length + 1) ^ 2 := by
  have scanBound := scanTime_le selected sources 0
  have countBound := selectedCount_le_length selected sources
  have bitsBound := trNat_length_le (selectedCount selected sources)
  unfold totalTime
  nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 5 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 5 * (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

/-- Counting selected symbols in binary and appending the result is
polynomial-time in the complete source-word length. -/
noncomputable def computableInPolyTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) :
    @TM2ComputableInPolyTime
      (List Source) (List (Source ⊕ PartrecToTM2.Γ'))
      Source (Source ⊕ PartrecToTM2.Γ') id id (paddedOutput selected) where
  tm := machine Source selected
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun sources := by
    have run := machine_outputsInTime selected sources
    have run' : TM2OutputsInTime (machine Source selected)
        (List.map (Equiv.refl Source).invFun (id sources))
        (some (List.map
          (Equiv.refl (Source ⊕ PartrecToTM2.Γ')).invFun
          (id (paddedOutput selected sources))))
        (totalTime selected sources) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    refine
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans ?_ }
    rw [timePolynomial_eval]
    exact totalTime_le Source selected sources

end BinaryCountPaddingMachine
end LeanTrominoes

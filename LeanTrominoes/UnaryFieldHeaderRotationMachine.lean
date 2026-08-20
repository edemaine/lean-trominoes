/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldHeaderRotation

/-! # Finite machine for unary strip-header rotation -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryFieldHeaderRotationMachine

open UnaryFieldEncoderMachine

inductive Stack
  | input
  | firstReverse
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanFirst
  | scanSecond
  | scanThird
  | emitFirst
  | copySuffix
  | reverseOutput
  deriving Fintype

abbrev State := Option Symbol

abbrev Alphabet : Stack → Type
  | _ => Symbol

def symbolFromState : State → Symbol
  | some symbol => symbol
  | none => default

def isUnitState : State → Bool
  | some .unit => true
  | _ => false

/-- Scan three unary fields, retaining the first and emitting the next two;
then emit the retained first field, copy the suffix, and reverse the output. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scanFirst =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          (.goto fun _ => .scanSecond)
          (.branch isUnitState
            (.push .firstReverse symbolFromState
              (.load (fun _ => none) (.goto fun _ => .scanFirst)))
            (.load (fun _ => none) (.goto fun _ => .scanSecond))))
  | .scanSecond =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .delimiter)
            (.goto fun _ => .scanThird))
          (.branch isUnitState
            (.push .outputReverse symbolFromState
              (.load (fun _ => none) (.goto fun _ => .scanSecond)))
            (.push .outputReverse (fun _ => .delimiter)
              (.load (fun _ => none) (.goto fun _ => .scanThird)))))
  | .scanThird =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .delimiter)
            (.goto fun _ => .emitFirst))
          (.branch isUnitState
            (.push .outputReverse symbolFromState
              (.load (fun _ => none) (.goto fun _ => .scanThird)))
            (.push .outputReverse (fun _ => .delimiter)
              (.load (fun _ => none) (.goto fun _ => .emitFirst)))))
  | .emitFirst =>
      .pop .firstReverse (fun _ symbol => symbol)
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .delimiter)
            (.goto fun _ => .copySuffix))
          (.push .outputReverse symbolFromState
            (.load (fun _ => none) (.goto fun _ => .emitFirst))))
  | .copySuffix =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.push .outputReverse symbolFromState
            (.load (fun _ => none) (.goto fun _ => .copySuffix))))
  | .reverseOutput =>
      .pop .outputReverse (fun _ symbol => symbol)
        (.branch Option.isNone
          .halt
          (.push .output symbolFromState
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanFirst
  σ := State
  initialState := none
  m := program

structure TapeData where
  input : List Symbol
  firstReverse : List Symbol
  outputReverse : List Symbol
  output : List Symbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .firstReverse => data.firstReverse
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def scanFirstCfg (data : TapeData) := cfg .scanFirst none data
def scanSecondCfg (data : TapeData) := cfg .scanSecond none data
def scanThirdCfg (data : TapeData) := cfg .scanThird none data
def emitFirstCfg (data : TapeData) := cfg .emitFirst none data
def copySuffixCfg (data : TapeData) := cfg .copySuffix none data
def reverseOutputCfg (data : TapeData) := cfg .reverseOutput none data

def haltCfg (output : List Symbol) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes ⟨[], [], [], output⟩⟩

def haltDataCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes data⟩

@[simp]
theorem update_tapes_input (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_firstReverse (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.firstReverse value =
      tapes { data with firstReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_outputReverse (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scanFirst_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanFirstCfg data) =
      some (scanSecondCfg { data with input := [] }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanFirstCfg, scanSecondCfg, cfg, tapes]

theorem step_scanFirst_unit (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanFirstCfg data) =
      some (scanFirstCfg
        { data with
          input := tail
          firstReverse := .unit :: data.firstReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = .unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanFirstCfg, cfg, tapes,
    isUnitState, symbolFromState]

theorem step_scanFirst_delimiter (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .delimiter :: tail) :
    TM2.step program (scanFirstCfg data) =
      some (scanSecondCfg { data with input := tail }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = .delimiter :: tail at inputEq
  subst input
  simp [TM2.step, program, scanFirstCfg, scanSecondCfg, cfg, tapes,
    isUnitState]

theorem step_scanSecond_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanSecondCfg data) =
      some (scanThirdCfg
        { data with
          input := []
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanSecondCfg, scanThirdCfg, cfg, tapes]

theorem step_scanSecond_unit (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanSecondCfg data) =
      some (scanSecondCfg
        { data with
          input := tail
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = .unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanSecondCfg, cfg, tapes,
    isUnitState, symbolFromState]

theorem step_scanSecond_delimiter (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .delimiter :: tail) :
    TM2.step program (scanSecondCfg data) =
      some (scanThirdCfg
        { data with
          input := tail
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = .delimiter :: tail at inputEq
  subst input
  simp [TM2.step, program, scanSecondCfg, scanThirdCfg, cfg, tapes,
    isUnitState]

theorem step_scanThird_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanThirdCfg data) =
      some (emitFirstCfg
        { data with
          input := []
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanThirdCfg, emitFirstCfg, cfg, tapes]

theorem step_scanThird_unit (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanThirdCfg data) =
      some (scanThirdCfg
        { data with
          input := tail
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = .unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanThirdCfg, cfg, tapes,
    isUnitState, symbolFromState]

theorem step_scanThird_delimiter (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .delimiter :: tail) :
    TM2.step program (scanThirdCfg data) =
      some (emitFirstCfg
        { data with
          input := tail
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = .delimiter :: tail at inputEq
  subst input
  simp [TM2.step, program, scanThirdCfg, emitFirstCfg, cfg, tapes,
    isUnitState]

theorem step_emitFirst_nil (data : TapeData)
    (firstEq : data.firstReverse = []) :
    TM2.step program (emitFirstCfg data) =
      some (copySuffixCfg
        { data with
          firstReverse := []
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change firstReverse = [] at firstEq
  subst firstReverse
  simp [TM2.step, program, emitFirstCfg, copySuffixCfg, cfg, tapes]

theorem step_emitFirst_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol) (firstEq : data.firstReverse = symbol :: tail) :
    TM2.step program (emitFirstCfg data) =
      some (emitFirstCfg
        { data with
          firstReverse := tail
          outputReverse := symbol :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change firstReverse = symbol :: tail at firstEq
  subst firstReverse
  cases symbol <;>
    simp [TM2.step, program, emitFirstCfg, cfg, tapes, symbolFromState]

theorem step_copySuffix_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (copySuffixCfg data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, copySuffixCfg, reverseOutputCfg, cfg, tapes]

theorem step_copySuffix_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol) (inputEq : data.input = symbol :: tail) :
    TM2.step program (copySuffixCfg data) =
      some (copySuffixCfg
        { data with
          input := tail
          outputReverse := symbol :: data.outputReverse }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change input = symbol :: tail at inputEq
  subst input
  cases symbol <;>
    simp [TM2.step, program, copySuffixCfg, cfg, tapes, symbolFromState]

theorem step_reverseOutput_nil (data : TapeData)
    (outputReverseEq : data.outputReverse = []) :
    TM2.step program (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol)
    (outputReverseEq : data.outputReverse = symbol :: tail) :
    TM2.step program (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := symbol :: data.output }) := by
  rcases data with ⟨input, firstReverse, outputReverse, output⟩
  change outputReverse = symbol :: tail at outputReverseEq
  subst outputReverse
  cases symbol <;>
    simp [TM2.step, program, reverseOutputCfg, cfg, tapes, symbolFromState]

end UnaryFieldHeaderRotationMachine
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.SeparatedProductEncoding

/-! # A finite machine for running two compilers on the same input -/

noncomputable section

namespace LeanTrominoes

open StateTransition Turing

namespace TM2ForkMachine

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

inductive Stack (First Second : Type)
  | input
  | inputReverse
  | first (stack : First)
  | second (stack : Second)
  | outputReverse
  | output
deriving DecidableEq, Fintype

inductive Label (First Second : Type)
  | drainInput
  | pushInputReverse
  | drainInputReverse
  | pushFirstInput
  | pushSecondInput
  | first (label : First)
  | second (label : Second)
  | drainFirstOutput
  | pushFirstOutput
  | pushSeparator
  | drainSecondOutput
  | pushSecondOutput
  | drainOutputReverse
  | pushOutput
  | finish
deriving Fintype

inductive State
    (First Second InputSymbol FirstSymbol SecondSymbol : Type)
  | setup (symbol : Option InputSymbol)
  | first (state : First)
  | second (state : Second)
  | firstOutput (symbol : Option FirstSymbol)
  | secondOutput (symbol : Option SecondSymbol)
  | output (symbol : Option (FirstSymbol ⊕ (Unit ⊕ SecondSymbol)))
deriving Fintype

abbrev OutputSymbol (FirstSymbol SecondSymbol : Type) :=
  FirstSymbol ⊕ (Unit ⊕ SecondSymbol)

def outputAlphabetEquiv (FirstSymbol SecondSymbol : Type) :
    OutputSymbol FirstSymbol SecondSymbol ≃
      SeparatedProductEncoding.Token FirstSymbol SecondSymbol where
  toFun
    | .inl symbol => .left symbol
    | .inr (.inl _) => .separator
    | .inr (.inr symbol) => .right symbol
  invFun
    | .left symbol => .inl symbol
    | .separator => .inr (.inl ())
    | .right symbol => .inr (.inr symbol)
  left_inv symbol := by cases symbol with
    | inl _ => rfl
    | inr symbol => cases symbol <;> rfl
  right_inv symbol := by cases symbol <;> rfl

abbrev Alphabet (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type) :
    Stack first.K second.K → Type
  | .input => InputSymbol
  | .inputReverse => InputSymbol
  | .first stack => first.Γ stack
  | .second stack => second.Γ stack
  | .outputReverse => OutputSymbol FirstSymbol SecondSymbol
  | .output => OutputSymbol FirstSymbol SecondSymbol

abbrev CombinedLabel (first second : FinTM2) :=
  Label first.Λ second.Λ

abbrev CombinedState (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type) :=
  State first.σ second.σ InputSymbol FirstSymbol SecondSymbol

def firstState (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol) :
    first.σ :=
  match state with
  | .first state => state
  | _ => first.initialState

def secondState (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol) :
    second.σ :=
  match state with
  | .second state => state
  | _ => second.initialState

def setupSymbol (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol) :
    Option InputSymbol :=
  match state with
  | .setup symbol => symbol
  | _ => none

def firstOutputSymbol (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol) :
    Option FirstSymbol :=
  match state with
  | .firstOutput symbol => symbol
  | _ => none

def secondOutputSymbol (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol) :
    Option SecondSymbol :=
  match state with
  | .secondOutput symbol => symbol
  | _ => none

def outputSymbol (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (state : CombinedState first second InputSymbol FirstSymbol SecondSymbol) :
    Option (OutputSymbol FirstSymbol SecondSymbol) :=
  match state with
  | .output symbol => symbol
  | _ => none

/-- Embed a statement of the first component.  Its halt starts the second
component on the already prepared input copy. -/
def embedFirstStatement (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type) :
    TM2.Stmt first.Γ first.Λ first.σ →
      TM2.Stmt (Alphabet first second InputSymbol FirstSymbol SecondSymbol)
        (CombinedLabel first second)
        (CombinedState first second InputSymbol FirstSymbol SecondSymbol)
  | .push stack write next =>
      .push (.first stack)
        (fun state => write
          (firstState first second InputSymbol FirstSymbol SecondSymbol state))
        (embedFirstStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .peek stack read next =>
      .peek (.first stack)
        (fun state symbol => .first (read
          (firstState first second InputSymbol FirstSymbol SecondSymbol state)
          symbol))
        (embedFirstStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .pop stack read next =>
      .pop (.first stack)
        (fun state symbol => .first (read
          (firstState first second InputSymbol FirstSymbol SecondSymbol state)
          symbol))
        (embedFirstStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .load update next =>
      .load (fun state => .first (update
        (firstState first second InputSymbol FirstSymbol SecondSymbol state)))
        (embedFirstStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .branch test yes no =>
      .branch (fun state => test
        (firstState first second InputSymbol FirstSymbol SecondSymbol state))
        (embedFirstStatement first second InputSymbol FirstSymbol SecondSymbol yes)
        (embedFirstStatement first second InputSymbol FirstSymbol SecondSymbol no)
  | .goto target =>
      .goto fun state => .first (target
        (firstState first second InputSymbol FirstSymbol SecondSymbol state))
  | .halt =>
      .load (fun _ => .second second.initialState)
        (.goto fun _ => .second second.main)

/-- Embed a statement of the second component.  Its halt starts assembly of
the two component outputs. -/
def embedSecondStatement (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type) :
    TM2.Stmt second.Γ second.Λ second.σ →
      TM2.Stmt (Alphabet first second InputSymbol FirstSymbol SecondSymbol)
        (CombinedLabel first second)
        (CombinedState first second InputSymbol FirstSymbol SecondSymbol)
  | .push stack write next =>
      .push (.second stack)
        (fun state => write
          (secondState first second InputSymbol FirstSymbol SecondSymbol state))
        (embedSecondStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .peek stack read next =>
      .peek (.second stack)
        (fun state symbol => .second (read
          (secondState first second InputSymbol FirstSymbol SecondSymbol state)
          symbol))
        (embedSecondStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .pop stack read next =>
      .pop (.second stack)
        (fun state symbol => .second (read
          (secondState first second InputSymbol FirstSymbol SecondSymbol state)
          symbol))
        (embedSecondStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .load update next =>
      .load (fun state => .second (update
        (secondState first second InputSymbol FirstSymbol SecondSymbol state)))
        (embedSecondStatement first second InputSymbol FirstSymbol SecondSymbol next)
  | .branch test yes no =>
      .branch (fun state => test
        (secondState first second InputSymbol FirstSymbol SecondSymbol state))
        (embedSecondStatement first second InputSymbol FirstSymbol SecondSymbol yes)
        (embedSecondStatement first second InputSymbol FirstSymbol SecondSymbol no)
  | .goto target =>
      .goto fun state => .second (target
        (secondState first second InputSymbol FirstSymbol SecondSymbol state))
  | .halt =>
      .load (fun _ => .firstOutput none)
        (.goto fun _ => .drainFirstOutput)

def program
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction) :
    CombinedLabel first.tm second.tm →
      TM2.Stmt
        (Alphabet first.tm second.tm InputSymbol FirstSymbol SecondSymbol)
        (CombinedLabel first.tm second.tm)
        (CombinedState first.tm second.tm InputSymbol FirstSymbol SecondSymbol)
  | .drainInput =>
      .pop .input (fun _ symbol => .setup symbol)
        (.goto fun state =>
          match setupSymbol first.tm second.tm
              InputSymbol FirstSymbol SecondSymbol state with
          | none => .drainInputReverse
          | some _ => .pushInputReverse)
  | .pushInputReverse =>
      .push .inputReverse (fun state =>
        (setupSymbol first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol state).getD default)
        (.load (fun _ => .setup none) (.goto fun _ => .drainInput))
  | .drainInputReverse =>
      .pop .inputReverse (fun _ symbol =>
        match symbol with
        | none => .first first.tm.initialState
        | some symbol => .setup (some symbol))
        (.goto fun state =>
          match setupSymbol first.tm second.tm
              InputSymbol FirstSymbol SecondSymbol state with
          | none => .first first.tm.main
          | some _ => .pushFirstInput)
  | .pushFirstInput =>
      .push (.first first.tm.k₀) (fun state =>
        first.inputAlphabet.invFun
          ((setupSymbol first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol state).getD default))
        (.goto fun _ => .pushSecondInput)
  | .pushSecondInput =>
      .push (.second second.tm.k₀) (fun state =>
        second.inputAlphabet.invFun
          ((setupSymbol first.tm second.tm
            InputSymbol FirstSymbol SecondSymbol state).getD default))
        (.load (fun _ => .setup none) (.goto fun _ => .drainInputReverse))
  | .first label =>
      embedFirstStatement first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol (first.tm.m label)
  | .second label =>
      embedSecondStatement first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol (second.tm.m label)
  | .drainFirstOutput =>
      .pop (.first first.tm.k₁) (fun _ symbol =>
        .firstOutput (symbol.map first.outputAlphabet))
        (.goto fun state =>
          match firstOutputSymbol first.tm second.tm
              InputSymbol FirstSymbol SecondSymbol state with
          | none => .pushSeparator
          | some _ => .pushFirstOutput)
  | .pushFirstOutput =>
      .push .outputReverse (fun state => .inl
        ((firstOutputSymbol first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol state).getD default))
        (.load (fun _ => .firstOutput none)
          (.goto fun _ => .drainFirstOutput))
  | .pushSeparator =>
      .push .outputReverse (fun _ => .inr (.inl ()))
        (.load (fun _ => .secondOutput none)
          (.goto fun _ => .drainSecondOutput))
  | .drainSecondOutput =>
      .pop (.second second.tm.k₁) (fun _ symbol =>
        .secondOutput (symbol.map second.outputAlphabet))
        (.goto fun state =>
          match secondOutputSymbol first.tm second.tm
              InputSymbol FirstSymbol SecondSymbol state with
          | none => .drainOutputReverse
          | some _ => .pushSecondOutput)
  | .pushSecondOutput =>
      .push .outputReverse (fun state => .inr (.inr
        ((secondOutputSymbol first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol state).getD default)))
        (.load (fun _ => .secondOutput none)
          (.goto fun _ => .drainSecondOutput))
  | .drainOutputReverse =>
      .pop .outputReverse (fun _ symbol => .output symbol)
        (.goto fun state =>
          match outputSymbol first.tm second.tm
              InputSymbol FirstSymbol SecondSymbol state with
          | none => .finish
          | some _ => .pushOutput)
  | .pushOutput =>
      .push .output (fun state =>
        (outputSymbol first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol state).getD
            (.inr (.inl ())))
        (.load (fun _ => .output none)
          (.goto fun _ => .drainOutputReverse))
  | .finish =>
      .load (fun _ => .setup none) .halt

/-- The finite machine that copies its input, runs both component machines,
and returns their separated pair of outputs. -/
def machine
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction) :
    FinTM2 where
  K := Stack first.tm.K second.tm.K
  kDecidableEq := instDecidableEqStack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet first.tm second.tm InputSymbol FirstSymbol SecondSymbol
  Γk₀Fin := inferInstance
  Λ := CombinedLabel first.tm second.tm
  main := .drainInput
  σ := CombinedState first.tm second.tm InputSymbol FirstSymbol SecondSymbol
  initialState := .setup none
  m := program first second

end TM2ForkMachine
end LeanTrominoes

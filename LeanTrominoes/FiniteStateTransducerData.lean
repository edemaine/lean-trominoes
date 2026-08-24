/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity

/-! # Finite-state word transducers -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace FiniteStateTransducer

/-- Scan a word from left to right, carrying finite control and concatenating
the finite word emitted at each transition. -/
def scan {Control Source Target : Type*}
    (transition : Control → Source → Control × List Target) :
    Control → List Source → Control × List Target
  | control, [] => (control, [])
  | control, symbol :: input =>
      let current := transition control symbol
      let rest := scan transition current.1 input
      (rest.1, current.2 ++ rest.2)

/-- Complete output, including the terminal word selected by the final
control state. -/
def output {Control Source Target : Type*}
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (input : List Source) : List Target :=
  let scanned := scan transition initial input
  scanned.2 ++ finish scanned.1

inductive Stack
  | input
  | accumulator
  | output
  deriving DecidableEq, Fintype

inductive Label (Control Source : Type)
  | scan (control : Control)
  | emit (control : Control) (symbol : Source)
  | finish (control : Control)
  | reverse
  deriving Fintype

abbrev State (Source Target : Type) := Option (Source ⊕ Target)

abbrev Alphabet (Source Target : Type) : Stack → Type
  | .input => Source
  | .accumulator | .output => Target

def pushWord {Control Source Target : Type}
    (word : List Target)
    (next : TM2.Stmt (Alphabet Source Target) (Label Control Source)
      (State Source Target)) :
    TM2.Stmt (Alphabet Source Target) (Label Control Source)
      (State Source Target) :=
  word.foldr
    (fun symbol continuation =>
      .push .accumulator (fun _ => symbol) continuation)
    next

def program {Control Source Target : Type} [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) :
    Label Control Source →
      TM2.Stmt (Alphabet Source Target) (Label Control Source)
        (State Source Target)
  | .scan control =>
      .pop .input (fun _ symbol => symbol.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .finish control)
          (.goto fun state =>
            match state with
            | some (.inl symbol) => .emit control symbol
            | _ => .finish control))
  | .emit control symbol =>
      pushWord (transition control symbol).2
        (.load (fun _ => none)
          (.goto fun _ => .scan (transition control symbol).1))
  | .finish control =>
      pushWord (finish control)
        (.load (fun _ => none) (.goto fun _ => .reverse))
  | .reverse =>
      .pop .accumulator (fun _ symbol => symbol.map Sum.inr)
        (.branch Option.isNone
          .halt
          (.push .output
            (fun state =>
              match state with
              | some (.inr symbol) => symbol
              | _ => default)
            (.load (fun _ => none) (.goto fun _ => .reverse))))

abbrev machine (Control Source Target : Type)
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Source Target
  Λ := Label Control Source
  main := .scan initial
  σ := State Source Target
  initialState := none
  m := program transition finish

def tapes {Source Target : Type}
    (input : List Source) (accumulator output : List Target) :
    ∀ stack, List (Alphabet Source Target stack)
  | .input => input
  | .accumulator => accumulator
  | .output => output

def scanCfg {Control Source Target : Type}
    (control : Control) (input : List Source) (accumulator : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Control Source)
      (State Source Target) :=
  ⟨some (.scan control), none, tapes input accumulator []⟩

def emitCfg {Control Source Target : Type}
    (control : Control) (symbol : Source) (input : List Source)
    (accumulator : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Control Source)
      (State Source Target) :=
  ⟨some (.emit control symbol), some (.inl symbol),
    tapes input accumulator []⟩

def finishCfg {Control Source Target : Type}
    (control : Control) (accumulator : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Control Source)
      (State Source Target) :=
  ⟨some (.finish control), none, tapes [] accumulator []⟩

def reverseCfg {Control Source Target : Type}
    (accumulator output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Control Source)
      (State Source Target) :=
  ⟨some .reverse, none, tapes [] accumulator output⟩

def haltCfg {Control Source Target : Type} (output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Control Source)
      (State Source Target) :=
  ⟨none, none, tapes [] [] output⟩

@[simp] theorem update_tapes_input {Source Target : Type}
    (head : Source) (input : List Source)
    (accumulator output : List Target) :
    Function.update (tapes (head :: input) accumulator output)
        Stack.input input =
      tapes input accumulator output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_accumulator {Source Target : Type}
    (input : List Source) (head : Target)
    (accumulator output : List Target) :
    Function.update (tapes input (head :: accumulator) output)
        Stack.accumulator accumulator =
      tapes input accumulator output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem push_tapes_accumulator {Source Target : Type}
    (input : List Source) (head : Target)
    (accumulator output : List Target) :
    Function.update (tapes input accumulator output)
        Stack.accumulator (head :: accumulator) =
      tapes input (head :: accumulator) output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushWord {Control Source Target : Type}
    (word : List Target)
    (next : TM2.Stmt (Alphabet Source Target) (Label Control Source)
      (State Source Target))
    (state : State Source Target)
    (input : List Source) (accumulator output : List Target) :
    TM2.stepAux (pushWord word next) state
        (tapes input accumulator output) =
      TM2.stepAux next state
        (tapes input (word.reverse ++ accumulator) output) := by
  induction word generalizing accumulator with
  | nil => simp [pushWord]
  | cons symbol word induction =>
      simp only [pushWord, List.foldr_cons, TM2.stepAux]
      simp only [tapes]
      rw [push_tapes_accumulator]
      change TM2.stepAux (pushWord word next) state
          (tapes input (symbol :: accumulator) output) =
        TM2.stepAux next state
          (tapes input ((symbol :: word).reverse ++ accumulator) output)
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem step_scan_cons {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (control : Control)
    (symbol : Source) (input : List Source) (accumulator : List Target) :
    TM2.step (program transition finish)
        (scanCfg control (symbol :: input) accumulator) =
      some (emitCfg control symbol input accumulator) := by
  simp [TM2.step, program, scanCfg, emitCfg, tapes]

theorem step_emit {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (control : Control)
    (symbol : Source) (input : List Source) (accumulator : List Target) :
    TM2.step (program transition finish)
        (emitCfg control symbol input accumulator) =
      some (scanCfg (transition control symbol).1 input
        ((transition control symbol).2.reverse ++ accumulator)) := by
  simp only [TM2.step, program, emitCfg, scanCfg]
  rw [stepAux_pushWord]
  rfl

theorem step_scan_nil {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (control : Control)
    (accumulator : List Target) :
    TM2.step (program transition finish) (scanCfg control [] accumulator) =
      some (finishCfg control accumulator) := by
  simp [TM2.step, program, scanCfg, finishCfg, tapes]

theorem step_finish {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (control : Control)
    (accumulator : List Target) :
    TM2.step (program transition finish) (finishCfg control accumulator) =
      some (reverseCfg ((finish control).reverse ++ accumulator) []) := by
  simp only [TM2.step, program, finishCfg, reverseCfg]
  rw [stepAux_pushWord]
  rfl

theorem step_reverse_cons {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (symbol : Target)
    (accumulator output : List Target) :
    TM2.step (program transition finish)
        (reverseCfg (symbol :: accumulator) output) =
      some (reverseCfg accumulator (symbol :: output)) := by
  simp [TM2.step, program, reverseCfg, tapes,
    update_tapes_accumulator]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_reverse_nil {Control Source Target : Type}
    [Fintype Control] [Fintype Source] [Fintype Target] [Inhabited Target]
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (output : List Target) :
    TM2.step (program transition finish) (reverseCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseCfg, haltCfg, tapes]

end FiniteStateTransducer
end LeanTrominoes

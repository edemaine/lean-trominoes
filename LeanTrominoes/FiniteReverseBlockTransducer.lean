/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer

/-! # Polynomial-time reverse finite block transducers

This two-stack machine scans its input from left to right and pushes each
fixed output block onto the output stack.  Stack order therefore reverses the
complete substituted word, with exact runtime `2 * input.length + 1`.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace FiniteReverseBlockTransducer

inductive Stack
  | input
  | output
deriving DecidableEq, Fintype

inductive Label (Source : Type)
  | scan
  | emit (symbol : Source)
deriving Fintype

abbrev State (Source : Type) := Option Source

abbrev Alphabet (Source Target : Type) : Stack → Type
  | .input => Source
  | .output => Target

def pushWord {Source Target : Type}
    (word : List Target)
    (next : TM2.Stmt (Alphabet Source Target) (Label Source)
      (State Source)) :
    TM2.Stmt (Alphabet Source Target) (Label Source)
      (State Source) :=
  word.foldr
    (fun symbol continuation =>
      .push .output (fun _ => symbol) continuation)
    next

def program {Source Target : Type}
    (word : Source → List Target) :
    Label Source →
      TM2.Stmt (Alphabet Source Target) (Label Source)
        (State Source)
  | .scan =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          .halt
          (.goto fun state =>
            match state with
            | some symbol => .emit symbol
            | none => .scan))
  | .emit symbol =>
      pushWord (word symbol)
        (.load (fun _ => none) (.goto fun _ => .scan))

abbrev machine (Source Target : Type)
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Source Target
  Λ := Label Source
  main := .scan
  σ := State Source
  initialState := none
  m := program word

def tapes {Source Target : Type}
    (input : List Source) (output : List Target) :
    ∀ stack, List (Alphabet Source Target stack)
  | .input => input
  | .output => output

def scanCfg {Source Target : Type}
    (input : List Source) (output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source) :=
  ⟨some .scan, none, tapes input output⟩

def emitCfg {Source Target : Type}
    (symbol : Source) (input : List Source)
    (output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source) :=
  ⟨some (.emit symbol), some symbol, tapes input output⟩

def haltCfg {Source Target : Type} (output : List Target) :
    TM2.Cfg (Alphabet Source Target) (Label Source)
      (State Source) :=
  ⟨none, none, tapes [] output⟩

@[simp] theorem update_tapes_input {Source Target : Type}
    (head : Source) (input : List Source) (output : List Target) :
    Function.update (tapes (head :: input) output)
        Stack.input input =
      tapes input output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem push_tapes_output {Source Target : Type}
    (input : List Source) (head : Target) (output : List Target) :
    Function.update (tapes input output)
        Stack.output (head :: output) =
      tapes input (head :: output) := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushWord {Source Target : Type}
    (word : List Target)
    (next : TM2.Stmt (Alphabet Source Target) (Label Source)
      (State Source))
    (state : State Source)
    (input : List Source) (output : List Target) :
    TM2.stepAux (pushWord word next) state (tapes input output) =
      TM2.stepAux next state
        (tapes input (word.reverse ++ output)) := by
  induction word generalizing output with
  | nil => simp [pushWord]
  | cons symbol word induction =>
      simp only [pushWord, List.foldr_cons, TM2.stepAux]
      simp only [tapes]
      rw [push_tapes_output]
      change TM2.stepAux (pushWord word next) state
          (tapes input (symbol :: output)) =
        TM2.stepAux next state
          (tapes input ((symbol :: word).reverse ++ output))
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem step_scan_cons {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (symbol : Source)
    (input : List Source) (output : List Target) :
    TM2.step (program word) (scanCfg (symbol :: input) output) =
      some (emitCfg symbol input output) := by
  simp [TM2.step, program, scanCfg, emitCfg, tapes]

theorem step_emit {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (symbol : Source)
    (input : List Source) (output : List Target) :
    TM2.step (program word) (emitCfg symbol input output) =
      some (scanCfg input ((word symbol).reverse ++ output)) := by
  simp only [TM2.step, program, emitCfg, scanCfg]
  rw [stepAux_pushWord]
  rfl

theorem step_scan_nil {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (output : List Target) :
    TM2.step (program word) (scanCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, scanCfg, haltCfg, tapes]

def scan_evalsInTime {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (input : List Source)
    (output : List Target) :
    EvalsToInTime (TM2.step (program word))
      (scanCfg input output)
      (some (haltCfg ((input.flatMap word).reverse ++ output)))
      (2 * input.length + 1) := by
  induction input generalizing output with
  | nil =>
      simpa using FiniteBlockTransducer.oneStep
        (step_scan_nil word output)
  | cons symbol input induction =>
      let emitted := (word symbol).reverse ++ output
      have popStep : EvalsToInTime (TM2.step (program word))
          (scanCfg (symbol :: input) output)
          (some (emitCfg symbol input output)) 1 :=
        FiniteBlockTransducer.oneStep
          (step_scan_cons word symbol input output)
      have emitStep : EvalsToInTime (TM2.step (program word))
          (emitCfg symbol input output)
          (some (scanCfg input emitted)) 1 :=
        FiniteBlockTransducer.oneStep
          (step_emit word symbol input output)
      have first := EvalsToInTime.trans _ 1 1 _ _ _ popStep emitStep
      have rest := induction emitted
      have target :
          (input.flatMap word).reverse ++ emitted =
            (((symbol :: input).flatMap word).reverse ++ output) := by
        simp [emitted, List.reverse_append, List.append_assoc]
      rw [target] at rest
      have composed := EvalsToInTime.trans _ 2
        (2 * input.length + 1) _ _ _ first rest
      convert composed using 1
      all_goals
        simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

theorem initList_eq_scanCfg {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (input : List Source) :
    initList (machine Source Target word) input = scanCfg input [] := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk (some (Label.scan)) none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

theorem haltList_eq_haltCfg {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (output : List Target) :
    haltList (machine Source Target word) output = haltCfg output := by
  apply congrArg (fun stackValues => TM2.Cfg.mk none none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

def outputsInExactTime {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) (input : List Source) :
    TM2OutputsInTime (machine Source Target word) input
      (some ((input.flatMap word).reverse))
      (2 * input.length + 1) := by
  change EvalsToInTime (TM2.step (program word))
    (initList (machine Source Target word) input)
    (some (haltList (machine Source Target word)
      ((input.flatMap word).reverse)))
    (2 * input.length + 1)
  rw [initList_eq_scanCfg word input, haltList_eq_haltCfg word]
  simpa using scan_evalsInTime word input []

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 1

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 2 * length + 1 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Reverse fixed block substitution is polynomial-time under native list
encodings. -/
noncomputable def computableInPolyTime
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    (word : Source → List Target) :
    TM2ComputableInPolyTime id id
      (fun input => (input.flatMap word).reverse) where
  tm := machine Source Target word
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun input := by
    simpa only [id_eq, FiniteBlockTransducer.map_refl_invFun,
      timePolynomial_eval] using outputsInExactTime word input

end FiniteReverseBlockTransducer

end LeanTrominoes

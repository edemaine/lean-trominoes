/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time closure for Boolean-valued compilers -/

noncomputable section

namespace LeanTrominoes
namespace TM2BooleanClosure

open Computability Turing

/-- Canonical singleton encoding of one Boolean result. -/
def booleanEncoding (value : Bool) : List Bool := [value]

def constantTransition {Source : Type} :
    Unit → Source → Unit × List Bool :=
  fun _ _ => ((), [])

def constantFinish (value : Bool) : Unit → List Bool :=
  fun _ => [value]

def constantWords {Source : Type}
    (value : Bool) (input : List Source) : List Bool :=
  FiniteStateTransducer.output () constantTransition
    (constantFinish value) input

@[simp] theorem constantScan {Source : Type} (input : List Source) :
    FiniteStateTransducer.scan constantTransition () input = ((), []) := by
  induction input with
  | nil => rfl
  | cons symbol input induction =>
      simp only [FiniteStateTransducer.scan, constantTransition, induction,
        List.nil_append]

@[simp] theorem constantWords_eq {Source : Type}
    (value : Bool) (input : List Source) :
    constantWords value input = [value] := by
  unfold constantWords FiniteStateTransducer.output
  rw [constantScan]
  rfl

/-- A constant Boolean-valued function is polynomial-time under every finite
input alphabet and encoding. -/
def constantComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol) (value : Bool) :
    TM2ComputableInPolyTime encodeInput booleanEncoding
      (fun _ : Input => value) := by
  let physical := FiniteStateTransducer.computableInPolyTime
    () (constantTransition (Source := InputSymbol)) (constantFinish value)
  let prepared : TM2ComputableInPolyTime encodeInput id
      (fun _ : Input => [value]) :=
    TM2PolyTimeInputEncodingTransport.of_prepare encodeInput physical
      (fun _ => rfl) (fun input => constantWords_eq value (encodeInput input))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (fun _ => rfl)

def unaryWords (operation : Bool → Bool) (input : List Bool) : List Bool :=
  input.flatMap fun value => [operation value]

@[simp] theorem unaryWords_singleton
    (operation : Bool → Bool) (value : Bool) :
    unaryWords operation [value] = [operation value] := by
  rfl

/-- Applying a fixed unary Boolean operation preserves polynomial time. -/
def unaryComputableInPolyTime (operation : Bool → Bool) :
    TM2ComputableInPolyTime booleanEncoding booleanEncoding operation := by
  let physical : TM2ComputableInPolyTime id id (unaryWords operation) :=
    FiniteBlockTransducer.computableInPolyTime
      (fun value => [operation value])
  let prepared : TM2ComputableInPolyTime booleanEncoding id
      (fun value => unaryWords operation [value]) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      (fun value => [value]) physical (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (fun value => unaryWords_singleton operation value)

def binaryTransition (operation : Bool → Bool → Bool) :
    Option Bool → SeparatedProductEncoding.Token Bool Bool →
      Option Bool × List Bool
  | _, .left first => (some first, [])
  | first, .separator => (first, [])
  | some first, .right second => (some first, [operation first second])
  | none, .right _ => (none, [])

def binaryWords (operation : Bool → Bool → Bool)
    (input : List (SeparatedProductEncoding.Token Bool Bool)) : List Bool :=
  FiniteStateTransducer.output none (binaryTransition operation)
    (fun _ => []) input

@[simp] theorem binaryWords_encoded
    (operation : Bool → Bool → Bool) (first second : Bool) :
    binaryWords operation
        (SeparatedProductEncoding.encode booleanEncoding booleanEncoding
          (first, second)) =
      [operation first second] := by
  cases first <;> cases second <;>
    rfl

/-- Applying a fixed binary Boolean operation to a separated pair is
polynomial-time. -/
def binaryComputableInPolyTime (operation : Bool → Bool → Bool) :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode booleanEncoding booleanEncoding)
      booleanEncoding (fun pair => operation pair.1 pair.2) := by
  let physical := FiniteStateTransducer.computableInPolyTime
    (none : Option Bool) (binaryTransition operation) (fun _ => [])
  let prepared : TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode booleanEncoding booleanEncoding) id
      (fun pair => [operation pair.1 pair.2]) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      (SeparatedProductEncoding.encode booleanEncoding booleanEncoding)
      physical (fun _ => rfl)
      (fun pair => binaryWords_encoded operation pair.1 pair.2)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (fun _ => rfl)

/-- Postcomposition by a unary Boolean operation. -/
def mapComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    {encodeInput : Input → List InputSymbol} {function : Input → Bool}
    (compiler :
      TM2ComputableInPolyTime encodeInput booleanEncoding function)
    (operation : Bool → Bool) :
    TM2ComputableInPolyTime encodeInput booleanEncoding
      (fun input => operation (function input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    (unaryComputableInPolyTime operation)

/-- Running two Boolean compilers on the same input and applying a fixed
binary operation preserves polynomial time. -/
def forkComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    {encodeInput : Input → List InputSymbol}
    {firstFunction secondFunction : Input → Bool}
    (first :
      TM2ComputableInPolyTime encodeInput booleanEncoding firstFunction)
    (second :
      TM2ComputableInPolyTime encodeInput booleanEncoding secondFunction)
    (operation : Bool → Bool → Bool) :
    TM2ComputableInPolyTime encodeInput booleanEncoding
      (fun input => operation (firstFunction input) (secondFunction input)) :=
  TM2CompositionMachine.computableInPolyTime
    (TM2ForkMachine.computableInPolyTime first second)
    (binaryComputableInPolyTime operation)

end TM2BooleanClosure
end LeanTrominoes

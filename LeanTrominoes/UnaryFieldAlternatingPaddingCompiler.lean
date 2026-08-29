/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Alternating zero padding of unary field lists -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldAlternatingPadding

open Computability Turing FiniteStateTransducer
open UnaryFieldEncoderMachine

def appendZeroValues (values : List Nat) : List Nat :=
  values.flatMap fun value => [value, 0]

def prependZeroValues (values : List Nat) : List Nat :=
  values.flatMap fun value => [0, value]

@[simp] theorem appendZeroValues_length (values : List Nat) :
    (appendZeroValues values).length = 2 * values.length := by
  simp [appendZeroValues, Nat.mul_comm]

@[simp] theorem prependZeroValues_length (values : List Nat) :
    (prependZeroValues values).length = 2 * values.length := by
  simp [prependZeroValues, Nat.mul_comm]

def appendZeroBlock : Symbol → List Symbol
  | .unit => [.unit]
  | .delimiter => [.delimiter, .delimiter]

def appendZeroOutput (symbols : List Symbol) : List Symbol :=
  symbols.flatMap appendZeroBlock

private theorem appendZeroOutput_unaryField (value : Nat) :
    appendZeroOutput (unaryField value) =
      unaryField value ++ unaryField 0 := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [unaryField, List.replicate_succ, List.cons_append]
      change .unit :: appendZeroOutput (unaryField value) = _
      rw [induction]
      simp [unaryField]

@[simp] theorem appendZeroOutput_unaryFields (values : List Nat) :
    appendZeroOutput (unaryFields values) =
      unaryFields (appendZeroValues values) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [unaryFields_cons, appendZeroValues, List.flatMap_cons]
      unfold appendZeroOutput at induction ⊢
      rw [List.flatMap_append, induction]
      rw [show List.flatMap appendZeroBlock (unaryField value) =
          unaryField value ++ unaryField 0 by
        exact appendZeroOutput_unaryField value]
      simp only [List.cons_append, List.nil_append, unaryFields_cons,
        List.append_assoc]
      rfl

def prependZeroTransition :
    Bool → Symbol → Bool × List Symbol
  | false, .unit => (true, [.delimiter, .unit])
  | false, .delimiter =>
      (false, [.delimiter, .delimiter])
  | true, .unit => (true, [.unit])
  | true, .delimiter => (false, [.delimiter])

def prependZeroFinish (_ : Bool) : List Symbol := []

def prependZeroOutput (symbols : List Symbol) : List Symbol :=
  FiniteStateTransducer.output false prependZeroTransition
    prependZeroFinish symbols

private theorem scan_fieldBody_unaryField (value : Nat) :
    scan prependZeroTransition true (unaryField value) =
      (false, unaryField value) := by
  induction value with
  | zero => rfl
  | succ value induction =>
      rw [unaryField, List.replicate_succ, List.cons_append]
      simp only [scan, prependZeroTransition]
      rw [← unaryField, induction]
      rfl

private theorem scan_fieldStart_unaryField (value : Nat) :
    scan prependZeroTransition false (unaryField value) =
      (false, unaryField 0 ++ unaryField value) := by
  cases value with
  | zero => rfl
  | succ value =>
      rw [unaryField, List.replicate_succ, List.cons_append]
      simp only [scan, prependZeroTransition]
      rw [← unaryField, scan_fieldBody_unaryField]
      rfl

private theorem scan_prependZero_unaryFields (values : List Nat) :
    scan prependZeroTransition false (unaryFields values) =
      (false, unaryFields (prependZeroValues values)) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [unaryFields_cons, scan_append,
        scan_fieldStart_unaryField]
      dsimp only
      rw [induction]
      rfl

@[simp] theorem prependZeroOutput_unaryFields (values : List Nat) :
    prependZeroOutput (unaryFields values) =
      unaryFields (prependZeroValues values) := by
  unfold prependZeroOutput FiniteStateTransducer.output
  rw [scan_prependZero_unaryFields]
  simp [prependZeroFinish]

private opaque appendZeroPhysicalComputableInPolyTime :
    TM2ComputableInPolyTime id id appendZeroOutput :=
  FiniteBlockTransducer.computableInPolyTime appendZeroBlock

private opaque prependZeroPhysicalComputableInPolyTime :
    TM2ComputableInPolyTime id id prependZeroOutput := by
  unfold prependZeroOutput
  exact FiniteStateTransducer.computableInPolyTime
    false prependZeroTransition prependZeroFinish

/-- Replacing each unary field by itself followed by zero is polynomial
time. -/
opaque appendZeroValuesComputableInPolyTime :
    TM2ComputableInPolyTime unaryFields unaryFields appendZeroValues := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    appendZeroPhysicalComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    appendZeroOutput_unaryFields

/-- Replacing each unary field by zero followed by itself is polynomial
time. -/
opaque prependZeroValuesComputableInPolyTime :
    TM2ComputableInPolyTime unaryFields unaryFields prependZeroValues := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    prependZeroPhysicalComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    prependZeroOutput_unaryFields

end UnaryFieldAlternatingPadding
end LeanTrominoes

end

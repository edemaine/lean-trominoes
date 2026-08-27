/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.OrthogonalPolylineRibbon
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Four-field unary direction decoding

An axis-aligned segment is represented by four unary lengths, in east,
north, west, south order.  This fixed transducer repeats that interpretation
for every consecutive group of four fields.
-/

noncomputable section

namespace LeanTrominoes.UnaryFourFieldDirections

open Computability Turing

inductive Control
  | east
  | north
  | west
  | south
  deriving DecidableEq, Fintype

def Control.direction : Control → AxisDirection
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south

def Control.next : Control → Control
  | .east => .north
  | .north => .west
  | .west => .south
  | .south => .east

def Control.advance : Control → Nat → Control
  | control, 0 => control
  | control, steps + 1 => (Control.next control).advance steps

/-- Interpret unary field lengths cyclically as east, north, west, and south
runs, starting at the supplied position in the cycle. -/
def directionsFrom : Control → List Nat → List AxisDirection
  | _, [] => []
  | control, value :: values =>
      List.replicate value control.direction ++
        directionsFrom control.next values

/-- Interpret complete four-field groups from the east position. -/
def directions (values : List Nat) : List AxisDirection :=
  directionsFrom .east values

def transition : Control → UnaryFieldEncoderMachine.Symbol →
    Control × List AxisDirection
  | control, .unit => (control, [control.direction])
  | control, .delimiter => (control.next, [])

def finish (_ : Control) : List AxisDirection := []

theorem scan_unaryField (control : Control) (value : Nat) :
    FiniteStateTransducer.scan transition control
        (UnaryFieldEncoderMachine.unaryField value) =
      (control.next, List.replicate value control.direction) := by
  induction value with
  | zero =>
      cases control <;> rfl
  | succ value induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [← UnaryFieldEncoderMachine.unaryField, induction]
      simp [List.replicate_succ]

theorem scan_unaryFields (control : Control) (values : List Nat) :
    FiniteStateTransducer.scan transition control
        (UnaryFieldEncoderMachine.unaryFields values) =
      (control.advance values.length, directionsFrom control values) := by
  induction values generalizing control with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append,
        scan_unaryField]
      dsimp
      rw [induction]
      simp [Control.advance, directionsFrom]

theorem output_unaryFields (values : List Nat) :
    FiniteStateTransducer.output .east transition finish
        (UnaryFieldEncoderMachine.unaryFields values) =
      directions values := by
  simp [FiniteStateTransducer.output, scan_unaryFields,
    finish, directions]

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Four consecutive unary fields are decoded as cardinal-direction runs by
a fixed finite-state transducer, hence in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id directions :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      Control.east transition finish)
    (fun _ => rfl) output_unaryFields

end LeanTrominoes.UnaryFourFieldDirections

end

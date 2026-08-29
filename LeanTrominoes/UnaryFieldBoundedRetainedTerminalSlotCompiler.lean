/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanBoundaryRouteFamily
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Compiling unary ranks to bounded retained-terminal slots -/

noncomputable section

namespace LeanTrominoes.BoundedRetainedTerminalSlots

open Computability Turing
open PeriodicEightOccurrenceSplit

abbrev Symbol := UnaryFieldEncoderMachine.Symbol
abbrev Slot := RetainedTerminalSlot

def zero : Slot := boundedRetainedTerminalSlot 0

def next (slot : Slot) : Slot :=
  boundedRetainedTerminalSlot (slot.val + 1)

def advance : Slot → Nat → Slot
  | slot, 0 => slot
  | slot, steps + 1 => advance (next slot) steps

def transition : Slot → Symbol → Slot × List Slot
  | slot, .unit => (next slot, [])
  | slot, .delimiter => (zero, [slot])

def finish (_ : Slot) : List Slot := []

def slots (ranks : List Nat) : List Slot :=
  ranks.map boundedRetainedTerminalSlot

@[simp] theorem next_boundedRetainedTerminalSlot (index : Nat) :
    next (boundedRetainedTerminalSlot index) =
      boundedRetainedTerminalSlot (index + 1) := by
  apply Fin.ext
  simp [next, boundedRetainedTerminalSlot]
  omega

theorem advance_boundedRetainedTerminalSlot
    (index steps : Nat) :
    advance (boundedRetainedTerminalSlot index) steps =
      boundedRetainedTerminalSlot (index + steps) := by
  induction steps generalizing index with
  | zero => simp [advance]
  | succ steps induction =>
      rw [advance, next_boundedRetainedTerminalSlot, induction]
      congr 1
      omega

theorem scan_unaryField (slot : Slot) (rank : Nat) :
    FiniteStateTransducer.scan transition slot
        (UnaryFieldEncoderMachine.unaryField rank) =
      (zero, [advance slot rank]) := by
  induction rank generalizing slot with
  | zero => rfl
  | succ rank induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [← UnaryFieldEncoderMachine.unaryField, induction]
      rfl

theorem scan_unaryFields (ranks : List Nat) :
    FiniteStateTransducer.scan transition zero
        (UnaryFieldEncoderMachine.unaryFields ranks) =
      (zero, slots ranks) := by
  induction ranks with
  | nil => rfl
  | cons rank ranks induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp only
      have advanceZero :
          advance zero rank = boundedRetainedTerminalSlot rank := by
        simpa [zero] using
          advance_boundedRetainedTerminalSlot 0 rank
      rw [advanceZero, induction]
      rfl

theorem output_unaryFields (ranks : List Nat) :
    FiniteStateTransducer.output zero transition finish
        (UnaryFieldEncoderMachine.unaryFields ranks) =
      slots ranks := by
  simp [FiniteStateTransducer.output, scan_unaryFields, finish]

/-- A saturated modulo-free counter converts every unary rank field to its
canonical bounded terminal slot in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id slots :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime zero transition finish)
    (fun _ => rfl) output_unaryFields

end LeanTrominoes.BoundedRetainedTerminalSlots

end

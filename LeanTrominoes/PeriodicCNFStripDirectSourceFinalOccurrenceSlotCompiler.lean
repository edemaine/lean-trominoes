/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceStableRankCompiler
import LeanTrominoes.PeriodicOneInThreeToThreeDMTyped
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Finite slots of final routed occurrences -/

noncomputable section

namespace LeanTrominoes

namespace BoundedOccurrenceSlots

open Computability Turing
open PeriodicOneInThreeToThreeDM

abbrev Symbol := UnaryFieldEncoderMachine.Symbol
abbrev Slot := OccurrenceSlot

instance : Inhabited Slot := ⟨.first⟩

/-- Saturate a zero-based rank to the three occurrence slots.  Valid final
formulas only exercise ranks zero through two. -/
def boundedOccurrenceSlot : Nat → Slot
  | 0 => .first
  | 1 => .second
  | _ => .third

def zero : Slot := .first

def next : Slot → Slot
  | .first => .second
  | .second | .third => .third

def advance : Slot → Nat → Slot
  | slot, 0 => slot
  | slot, steps + 1 => advance (next slot) steps

def transition : Slot → Symbol → Slot × List Slot
  | slot, .unit => (next slot, [])
  | slot, .delimiter => (zero, [slot])

def finish (_ : Slot) : List Slot := []

def slots (ranks : List Nat) : List Slot :=
  ranks.map boundedOccurrenceSlot

@[simp] theorem next_boundedOccurrenceSlot (index : Nat) :
    next (boundedOccurrenceSlot index) =
      boundedOccurrenceSlot (index + 1) := by
  rcases index with _ | _ | index <;> rfl

theorem advance_boundedOccurrenceSlot (index steps : Nat) :
    advance (boundedOccurrenceSlot index) steps =
      boundedOccurrenceSlot (index + steps) := by
  induction steps generalizing index with
  | zero => simp [advance]
  | succ steps induction =>
      rw [advance, next_boundedOccurrenceSlot, induction]
      congr 1
      omega

/-- On valid ranks, the finite slot preserves the exact zero-based index. -/
theorem boundedOccurrenceSlot_index_of_lt_three
    (index : Nat) (indexLt : index < 3) :
    (boundedOccurrenceSlot index).index = index := by
  interval_cases index <;> rfl

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
          advance zero rank = boundedOccurrenceSlot rank := by
        rw [show zero = boundedOccurrenceSlot 0 by rfl,
          advance_boundedOccurrenceSlot, Nat.zero_add]
      rw [advanceZero, induction]
      rfl

theorem output_unaryFields (ranks : List Nat) :
    FiniteStateTransducer.output zero transition finish
        (UnaryFieldEncoderMachine.unaryFields ranks) =
      slots ranks := by
  simp [FiniteStateTransducer.output, scan_unaryFields, finish]

/-- A three-state saturating counter converts unary ranks to occurrence slots
in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id slots :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime zero transition finish)
    (fun _ => rfl) output_unaryFields

end BoundedOccurrenceSlots

namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceSlotStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One finite variable-fan slot per final routed occurrence. -/
def directSourceFinalOccurrenceSlots
    (symbols : List encoding.Γ) : List OccurrenceSlot :=
  BoundedOccurrenceSlots.slots
    (directSourceFinalOccurrenceStableRanks decider symbols)

@[simp] theorem directSourceFinalOccurrenceSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceSlots decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceSlots BoundedOccurrenceSlots.slots
  rw [List.length_map,
    directSourceFinalOccurrenceStableRanks_length]

/-- Final occurrence slots are polynomial-time computable from direct source
symbols. -/
noncomputable def directSourceFinalOccurrenceSlotsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalOccurrenceSlots decider) := by
  unfold directSourceFinalOccurrenceSlots
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceStableRanksComputableInPolyTime decider)
    BoundedOccurrenceSlots.computableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end

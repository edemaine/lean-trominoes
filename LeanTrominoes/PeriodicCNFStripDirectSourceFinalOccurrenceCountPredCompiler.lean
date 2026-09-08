/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceGroupSizeCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Finite predecessors of final occurrence-group sizes -/

noncomputable section

namespace LeanTrominoes

namespace BoundedPositiveCountPreds

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- Four states distinguish zero, one, two, and at least three unary units.
Only the last three states occur for final atom multiplicities. -/
inductive State
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Fintype

-- An explicit default avoids a code-generation failure in the derived instance.
instance : Inhabited State := ⟨.zero⟩

/-- Saturated state reached after reading a unary field of the given size. -/
def stateOfCount : Nat → State
  | 0 => .zero
  | 1 => .one
  | 2 => .two
  | _ => .three

/-- Saturated predecessor expected by `VariableRibbonFanData.countPred`.
The harmless zero-size fallback agrees with the one-occurrence value. -/
def boundedPositiveCountPred : Nat → Fin 3
  | 0 | 1 => 0
  | 2 => 1
  | _ => 2

def State.next : State → State
  | .zero => .one
  | .one => .two
  | .two | .three => .three

def State.countPred : State → Fin 3
  | .zero | .one => 0
  | .two => 1
  | .three => 2

def State.advance : State → Nat → State
  | state, 0 => state
  | state, steps + 1 => State.advance state.next steps

def transition : State → Symbol → State × List (Fin 3)
  | state, .unit => (state.next, [])
  | state, .delimiter => (.zero, [state.countPred])

def finish (_ : State) : List (Fin 3) := []

def countPreds (counts : List Nat) : List (Fin 3) :=
  counts.map boundedPositiveCountPred

@[simp] theorem State.next_stateOfCount (count : Nat) :
    (stateOfCount count).next = stateOfCount (count + 1) := by
  cases count with
  | zero => rfl
  | succ count =>
      cases count with
      | zero => rfl
      | succ count =>
          cases count <;> rfl

@[simp] theorem State.countPred_stateOfCount (count : Nat) :
    (stateOfCount count).countPred = boundedPositiveCountPred count := by
  cases count with
  | zero => rfl
  | succ count =>
      cases count with
      | zero => rfl
      | succ count =>
          cases count <;> rfl

theorem State.advance_stateOfCount (count steps : Nat) :
    (stateOfCount count).advance steps = stateOfCount (count + steps) := by
  induction steps generalizing count with
  | zero => simp [State.advance]
  | succ steps induction =>
      rw [State.advance, State.next_stateOfCount, induction]
      congr 1
      omega

/-- On the semantic one-to-three range, the finite predecessor recovers the
exact positive occurrence count. -/
theorem boundedPositiveCountPred_add_one_of_pos_le_three
    (count : Nat) (positive : 0 < count) (atMostThree : count ≤ 3) :
    (boundedPositiveCountPred count).val + 1 = count := by
  interval_cases count <;> rfl

theorem scan_unaryField (state : State) (count : Nat) :
    FiniteStateTransducer.scan transition state
        (UnaryFieldEncoderMachine.unaryField count) =
      (.zero, [(state.advance count).countPred]) := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [← UnaryFieldEncoderMachine.unaryField, induction]
      rfl

theorem scan_unaryFields (counts : List Nat) :
    FiniteStateTransducer.scan transition .zero
        (UnaryFieldEncoderMachine.unaryFields counts) =
      (.zero, countPreds counts) := by
  induction counts with
  | nil => rfl
  | cons count counts induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp only
      rw [show State.zero.advance count = stateOfCount count by
          rw [show State.zero = stateOfCount 0 by rfl,
            State.advance_stateOfCount, Nat.zero_add],
        State.countPred_stateOfCount, induction]
      rfl

theorem output_unaryFields (counts : List Nat) :
    FiniteStateTransducer.output State.zero transition finish
        (UnaryFieldEncoderMachine.unaryFields counts) =
      countPreds counts := by
  simp [FiniteStateTransducer.output, scan_unaryFields, finish]

/-- A four-state transducer converts unary positive counts to the finite fan
count-predecessor alphabet in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id countPreds :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      State.zero transition finish)
    (fun _ => rfl) output_unaryFields

end BoundedPositiveCountPreds

namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalOccurrenceCountPredStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One finite variable-fan count predecessor per final routed occurrence. -/
def directSourceFinalOccurrenceCountPreds
    (symbols : List encoding.Γ) : List (Fin 3) :=
  BoundedPositiveCountPreds.countPreds
    (directSourceFinalOccurrenceGroupSizes decider symbols)

/-- The emitted predecessor is the saturated predecessor of the ordinary
multiplicity of the occurrence's injective identity word. -/
theorem directSourceFinalOccurrenceCountPreds_eq
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceCountPreds decider symbols =
      (directSourceFinalAtomIdentityWords decider symbols).words.map
        fun word => BoundedPositiveCountPreds.boundedPositiveCountPred
          ((directSourceFinalAtomIdentityWords decider symbols).words.count
            word) := by
  unfold directSourceFinalOccurrenceCountPreds
    BoundedPositiveCountPreds.countPreds
  rw [directSourceFinalOccurrenceGroupSizes_eq, List.map_map]
  simp [Function.comp_def]

@[simp] theorem directSourceFinalOccurrenceCountPreds_length
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceCountPreds decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalOccurrenceCountPreds
    BoundedPositiveCountPreds.countPreds
  rw [List.length_map,
    directSourceFinalOccurrenceGroupSizes_length]

/-- Final occurrence count predecessors are polynomial-time computable from
direct source symbols. -/
noncomputable def directSourceFinalOccurrenceCountPredsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalOccurrenceCountPreds decider) := by
  unfold directSourceFinalOccurrenceCountPreds
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceGroupSizesComputableInPolyTime decider)
    BoundedPositiveCountPreds.computableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionCompilerData
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Decoding unary retained-terminal direction ranks -/

noncomputable section

namespace LeanTrominoes
namespace RetainedTerminalDirectionRankDecoder

open Computability Turing FiniteStateTransducer
open PeriodicEightOccurrenceSplit

abbrev Symbol := UnaryFieldEncoderMachine.Symbol
abbrev Control := Fin 11

def boundedRank (rank : Nat) : Control :=
  ⟨min rank 10, by omega⟩

def initial : Control := boundedRank 0

def increment (control : Control) : Control :=
  boundedRank (control.val + 1)

def advance : Control → Nat → Control
  | control, 0 => control
  | control, steps + 1 => advance (increment control) steps

/-- Malformed oversized fields saturate to rank ten. -/
def directionOfRank (rank : Nat) : RetainedTerminalDirection :=
  retainedTerminalDirections.getD (min rank 10) (.compass .east)

def directionsOfRanks (ranks : List Nat) :
    List RetainedTerminalDirection :=
  ranks.map directionOfRank

def transition :
    Control → Symbol → Control × List RetainedTerminalDirection
  | control, .unit => (increment control, [])
  | control, .delimiter =>
      (initial,
        [retainedTerminalDirections.getD
          control.val (.compass .east)])

def finish (_ : Control) : List RetainedTerminalDirection := []

def output (symbols : List Symbol) :
    List RetainedTerminalDirection :=
  FiniteStateTransducer.output initial transition finish symbols

private theorem increment_boundedRank (rank : Nat) :
    increment (boundedRank rank) = boundedRank (rank + 1) := by
  apply Fin.ext
  simp only [increment, boundedRank, Fin.val_mk]
  omega

private theorem advance_boundedRank (rank steps : Nat) :
    advance (boundedRank rank) steps = boundedRank (rank + steps) := by
  induction steps generalizing rank with
  | zero => rfl
  | succ steps induction =>
      rw [show advance (boundedRank rank) (steps + 1) =
          advance (increment (boundedRank rank)) steps by rfl]
      rw [increment_boundedRank, induction]
      congr 1
      omega

private theorem scan_unaryField (control : Control) (rank : Nat) :
    scan transition control
        (UnaryFieldEncoderMachine.unaryField rank) =
      (initial,
        [retainedTerminalDirections.getD
          (advance control rank).val (.compass .east)]) := by
  induction rank generalizing control with
  | zero => rfl
  | succ rank induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [scan, transition]
      rw [← UnaryFieldEncoderMachine.unaryField]
      exact induction (increment control)

private theorem scan_unaryFields (ranks : List Nat) :
    scan transition initial
        (UnaryFieldEncoderMachine.unaryFields ranks) =
      (initial, directionsOfRanks ranks) := by
  induction ranks with
  | nil => rfl
  | cons rank ranks induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        scan_append, scan_unaryField]
      dsimp only
      have advanced :
          advance initial rank = boundedRank rank := by
        simpa [initial] using advance_boundedRank 0 rank
      rw [advanced, induction]
      rfl

@[simp] theorem output_unaryFields (ranks : List Nat) :
    output (UnaryFieldEncoderMachine.unaryFields ranks) =
      directionsOfRanks ranks := by
  unfold output FiniteStateTransducer.output
  rw [scan_unaryFields]
  simp [finish]

@[simp] theorem directionOfRank_angularRank
    (direction : RetainedTerminalDirection) :
    directionOfRank direction.angularRank = direction := by
  cases direction with
  | compass port => cases port <;> rfl
  | routedClause arm => cases arm <;> rfl

private noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

/-- Unary angular-rank fields decode to their saturated native terminal
directions in polynomial time. -/
noncomputable def directionsOfRanksComputableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id directionsOfRanks :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    outputComputableInPolyTime
    (fun _ => rfl) output_unaryFields

end RetainedTerminalDirectionRankDecoder
end LeanTrominoes

end

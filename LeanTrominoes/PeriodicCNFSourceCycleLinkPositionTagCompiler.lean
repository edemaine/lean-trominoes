/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFSourceCycleLinkPositionTags
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Polynomial-time source cycle-link position tags -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

open Computability Turing

inductive Control
  | empty
  | one
  | many
  deriving DecidableEq, Fintype

def transition : Control → UnaryFieldEncoderMachine.Symbol →
    Control × List Tag
  | .empty => fun
      | .unit => (.one, [])
      | .delimiter => (.empty, [])
  | .one => fun
      | .unit => (.many, [.first])
      | .delimiter => (.empty, [.singleton])
  | .many => fun
      | .unit => (.many, [.middle])
      | .delimiter => (.empty, [.last])

def finish : Control → List Tag
  | .empty => []
  | .one => [.singleton]
  | .many => [.last]

theorem scan_many (count : Nat) :
    FiniteStateTransducer.scan transition .many
        (List.replicate count .unit ++ [.delimiter]) =
      (.empty, List.replicate count .middle ++ [.last]) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction]
      rw [List.replicate_succ]
      rfl

theorem scan_unaryField (groupSize : Nat) :
    FiniteStateTransducer.scan transition .empty
        (UnaryFieldEncoderMachine.unaryField groupSize) =
      (.empty, groupTags groupSize) := by
  cases groupSize with
  | zero => rfl
  | succ groupSize =>
      cases groupSize with
      | zero => rfl
      | succ count =>
          simp only [UnaryFieldEncoderMachine.unaryField,
            List.replicate_succ, List.cons_append,
            FiniteStateTransducer.scan, transition]
          rw [scan_many]
          rfl

theorem scan_unaryFields (groupSizes : List Nat) :
    FiniteStateTransducer.scan transition .empty
        (UnaryFieldEncoderMachine.unaryFields groupSizes) =
      (.empty, tags groupSizes) := by
  induction groupSizes with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp
      rw [induction]
      rfl

theorem output_unaryFields (groupSizes : List Nat) :
    FiniteStateTransducer.output .empty transition finish
        (UnaryFieldEncoderMachine.unaryFields groupSizes) =
      tags groupSizes := by
  simp [FiniteStateTransducer.output, scan_unaryFields, finish]

/-- Unary group sizes are converted to one finite boundary tag per link in
polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id tags :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    UnaryFieldEncoderMachine.unaryFields
    (FiniteStateTransducer.computableInPolyTime
      Control.empty transition finish)
    (fun _ => rfl) output_unaryFields

end LeanTrominoes.PeriodicCNF.SourceCycleLinkPositionTags

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import Mathlib.Data.Fintype.Vector

/-! # Finite-control evaluation of fixed-length words -/

noncomputable section

namespace LeanTrominoes
namespace FixedLengthWordEvaluator

open Computability Turing

/-- Shift the stored fixed-length word left and append the newest symbol. -/
def shiftAppend {Source : Type} :
    {length : Nat} → List.Vector Source length → Source →
      List.Vector Source length
  | 0, _, _ => List.Vector.nil
  | _ + 1, stored, symbol =>
      ⟨stored.toList.tail ++ [symbol], by
        simp only [List.length_append, List.length_tail,
          List.Vector.toList_length, List.length_singleton]
        omega⟩

/-- Store a source symbol without emitting intermediate output. -/
def transition {Source Target : Type} {length : Nat} :
    List.Vector Source length → Source →
      List.Vector Source length × List Target :=
  fun stored symbol => (shiftAppend stored symbol, [])

/-- Default-filled storage followed by an already-read prefix. -/
def paddedVector {Source : Type} {length : Nat}
    (default : Source) (prior suffix : List Source)
    (lengthEq : prior.length + suffix.length = length) :
    List.Vector Source length :=
  ⟨List.replicate suffix.length default ++ prior, by
    simp only [List.length_append, List.length_replicate]
    omega⟩

/-- Scanning the unread suffix shifts out every default cell and leaves the
prefix followed by that suffix. -/
theorem scan_paddedVector {Source Target : Type} {length : Nat}
    (default : Source) (prior suffix : List Source)
    (lengthEq : prior.length + suffix.length = length) :
    FiniteStateTransducer.scan
        (transition (Target := Target))
        (paddedVector default prior suffix lengthEq) suffix =
      (⟨prior ++ suffix, by
        simp only [List.length_append]
        exact lengthEq⟩,
      []) := by
  induction suffix generalizing prior with
  | nil =>
      apply Prod.ext
      · apply List.Vector.eq
        simp only [FiniteStateTransducer.scan, paddedVector,
          List.Vector.toList_mk, List.length_nil, List.replicate_zero,
          List.nil_append, List.append_nil]
      · rfl
  | cons symbol suffix induction =>
      simp only [FiniteStateTransducer.scan, transition, List.nil_append]
      have nextLengthEq :
          (prior ++ [symbol]).length + suffix.length = length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at lengthEq ⊢
        omega
      have shifted :
          shiftAppend (paddedVector default prior (symbol :: suffix)
            lengthEq) symbol =
            paddedVector default (prior ++ [symbol]) suffix
              nextLengthEq := by
        cases length with
        | zero =>
            simp only [List.length_cons] at lengthEq
            omega
        | succ remaining =>
            apply List.Vector.eq
            simp [shiftAppend, paddedVector, List.append_assoc]
      rw [shifted, induction (prior ++ [symbol]) nextLengthEq]
      apply Prod.ext
      · apply List.Vector.eq
        simp only [List.Vector.toList_mk, List.append_assoc,
          List.singleton_append]
      · rfl

/-- Run a fixed terminal function after retaining the complete source word in
finite control. -/
def output {Source Target : Type} [Inhabited Source]
    (length : Nat) (finish : List Source → List Target)
    (input : List Source) : List Target :=
  FiniteStateTransducer.output (List.Vector.replicate length default)
    (transition (Target := Target))
    (fun stored => finish stored.toList) input

/-- On a word of the prescribed length, the finite-control evaluator applies
its terminal function to that word exactly. -/
theorem output_eq_of_length_eq {Source Target : Type} [Inhabited Source]
    (length : Nat) (finish : List Source → List Target)
    (input : List Source) (lengthEq : input.length = length) :
    output length finish input = finish input := by
  unfold output FiniteStateTransducer.output
  have initialEq :
      List.Vector.replicate length (default : Source) =
        paddedVector default [] input (by simpa using lengthEq) := by
    apply List.Vector.eq
    simp only [List.Vector.replicate, List.Vector.toList_mk,
      paddedVector, List.Vector.toList_mk, List.append_nil]
    rw [lengthEq]
  rw [initialEq, scan_paddedVector]
  rfl

/-- Every terminal function on words of one fixed length is realized by a
polynomial-time finite-state transducer. -/
def computableInPolyTime {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    (length : Nat) (finish : List Source → List Target) :
    TM2ComputableInPolyTime id id (output length finish) :=
  FiniteStateTransducer.computableInPolyTime
    (List.Vector.replicate length default)
    (transition (Target := Target))
    (fun stored => finish stored.toList)

end FixedLengthWordEvaluator
end LeanTrominoes

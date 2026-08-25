/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFixedControlAugmenter
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Exact semantics of fixed-control word-pair augmentation -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPairFixedControlAugmenter

open DelimitedBinaryWordPairs

def augmentFirst (amount : Nat) (control : Bool)
    (first : List Bool) : List Bool :=
  (if control then List.replicate amount false else []) ++ first

def augmentPair (amount : Nat) (control : Bool)
    (pair : List Bool × List Bool) : List Bool × List Bool :=
  (augmentFirst amount control pair.1, pair.2)

def augmentPairs (amount : Nat) (controls : List Bool)
    (pairs : List (List Bool × List Bool)) :
    List (List Bool × List Bool) :=
  List.zipWith (augmentPair amount) controls pairs

theorem scan_left (amount controlCount : Nat)
    (stored : List.Vector Bool controlCount) (controls : List Bool) :
    FiniteStateTransducer.scan (transition amount controlCount)
        ⟨stored, true⟩ (controls.map .left) =
      let scanned := FiniteStateTransducer.scan
        (FixedLengthWordEvaluator.transition
          (Target := DelimitedBinaryWordPairs.Token))
        stored controls
      (⟨scanned.1, true⟩, scanned.2) := by
  induction controls generalizing stored with
  | nil => rfl
  | cons control controls induction =>
      simpa [FiniteStateTransducer.scan, transition,
        FixedLengthWordEvaluator.transition] using
        induction
          (FixedLengthWordEvaluator.shiftAppend stored control)

theorem scan_left_initial (amount controlCount : Nat)
    (controls : List Bool) (lengthEq : controls.length = controlCount) :
    FiniteStateTransducer.scan (transition amount controlCount)
        (initialState controlCount) (controls.map .left) =
      (⟨(⟨controls, by simpa using lengthEq⟩ :
          List.Vector Bool controlCount), true⟩, []) := by
  unfold initialState
  rw [scan_left]
  have initialEq : List.Vector.replicate controlCount false =
      FixedLengthWordEvaluator.paddedVector false [] controls
        (by simpa using lengthEq) := by
    apply List.Vector.eq
    simp only [List.Vector.replicate, List.Vector.toList_mk,
      FixedLengthWordEvaluator.paddedVector, List.append_nil]
    rw [lengthEq]
  rw [initialEq, FixedLengthWordEvaluator.scan_paddedVector]
  rfl

theorem scan_firstBits (amount controlCount : Nat)
    (state : State controlCount) (bits : List Bool)
    (readingEq : state.readingControls = false) :
    FiniteStateTransducer.scan (transition amount controlCount) state
        ((bits.map .firstBit).map .right) =
      (state, bits.map .firstBit) := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit bits induction =>
      have rest := induction state readingEq
      simp only [List.map_cons, FiniteStateTransducer.scan]
      rw [show transition amount controlCount state
          (.right (.firstBit bit)) = (state, [.firstBit bit]) by
        simp [transition, readingEq]]
      simp only [List.singleton_append]
      rw [rest]

theorem scan_secondBits (amount controlCount : Nat)
    (state : State controlCount) (bits : List Bool)
    (readingEq : state.readingControls = false) :
    FiniteStateTransducer.scan (transition amount controlCount) state
        ((bits.map .secondBit).map .right) =
      (state, bits.map .secondBit) := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit bits induction =>
      have rest := induction state readingEq
      simp only [List.map_cons, FiniteStateTransducer.scan]
      rw [show transition amount controlCount state
          (.right (.secondBit bit)) = (state, [.secondBit bit]) by
        simp [transition, readingEq]]
      simp only [List.singleton_append]
      rw [rest]

theorem scan_pairTokens (amount controlCount : Nat)
    (state : State controlCount) (pair : List Bool × List Bool)
    (readingEq : state.readingControls = false) :
    FiniteStateTransducer.scan (transition amount controlCount) state
        ((pairTokens pair).map .right) =
      (advance state,
        pairTokens (augmentPair amount (currentControl state) pair)) := by
  rcases pair with ⟨first, second⟩
  by_cases control : currentControl state
  · simp only [pairTokens, List.map_cons, List.map_append,
      FiniteStateTransducer.scan]
    rw [show transition amount controlCount state (.right .pairStart) =
        (state, [.pairStart] ++
          List.replicate amount (.firstBit false)) by
      simp [transition, readingEq, control]]
    rw [FiniteStateTransducer.scan_append,
      scan_firstBits amount controlCount state first readingEq]
    simp only [List.singleton_append,
      FiniteStateTransducer.scan]
    rw [show transition amount controlCount state (.right .middle) =
        (state, [.middle]) by simp [transition, readingEq]]
    rw [FiniteStateTransducer.scan_append,
      scan_secondBits amount controlCount state second readingEq]
    simp only [List.singleton_append,
      FiniteStateTransducer.scan]
    rw [show transition amount controlCount state (.right .pairEnd) =
        (advance state, [.pairEnd]) by simp [transition, readingEq]]
    simp [augmentPair, augmentFirst, control,
      FiniteStateTransducer.scan, List.append_assoc]
  · simp only [pairTokens, List.map_cons, List.map_append,
      FiniteStateTransducer.scan]
    rw [show transition amount controlCount state (.right .pairStart) =
        (state, [.pairStart]) by simp [transition, readingEq, control]]
    rw [FiniteStateTransducer.scan_append,
      scan_firstBits amount controlCount state first readingEq]
    simp only [List.singleton_append,
      FiniteStateTransducer.scan]
    rw [show transition amount controlCount state (.right .middle) =
        (state, [.middle]) by simp [transition, readingEq]]
    rw [FiniteStateTransducer.scan_append,
      scan_secondBits amount controlCount state second readingEq]
    simp only [List.singleton_append,
      FiniteStateTransducer.scan]
    rw [show transition amount controlCount state (.right .pairEnd) =
        (advance state, [.pairEnd]) by simp [transition, readingEq]]
    simp [augmentPair, augmentFirst, control, FiniteStateTransducer.scan]

theorem advance_readingControls {controlCount : Nat}
    (state : State controlCount) :
    (advance state).readingControls = state.readingControls :=
  rfl

end DelimitedBinaryWordPairFixedControlAugmenter
end LeanTrominoes

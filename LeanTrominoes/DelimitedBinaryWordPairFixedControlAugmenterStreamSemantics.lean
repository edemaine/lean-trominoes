/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFixedControlAugmenterSemantics

/-! # Stream semantics of fixed-control word-pair augmentation -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPairFixedControlAugmenter

open DelimitedBinaryWordPairs

theorem advance_controls_toList_of_ne_zero {controlCount : Nat}
    (state : State controlCount) (nonzero : controlCount ≠ 0) :
    (advance state).controls.toList =
      state.controls.toList.tail ++ [false] := by
  cases controlCount with
  | zero => exact (nonzero rfl).elim
  | succ controlCount => rfl

theorem currentControl_eq_head {controlCount : Nat}
    (state : State controlCount) (control : Bool)
    (controls : List Bool) (padding : List Bool)
    (controlsEq : state.controls.toList =
      control :: controls ++ padding) :
    currentControl state = control := by
  simp [currentControl, controlsEq]

theorem scan_pairs (amount controlCount : Nat)
    (state : State controlCount) (controls padding : List Bool)
    (pairs : List (List Bool × List Bool))
    (readingEq : state.readingControls = false)
    (controlsEq : state.controls.toList = controls ++ padding)
    (lengthEq : controls.length = pairs.length) :
    ∃ finalState,
      FiniteStateTransducer.scan (transition amount controlCount) state
          ((encode ⟨pairs⟩).map .right) =
        (finalState, encode ⟨augmentPairs amount controls pairs⟩) := by
  induction pairs generalizing state controls padding with
  | nil =>
      have controlsNil : controls = [] := by
        simpa using lengthEq
      subst controls
      exact ⟨state, rfl⟩
  | cons pair pairs induction =>
      cases controls with
      | nil => simp at lengthEq
      | cons control controls =>
          have tailLengthEq : controls.length = pairs.length := by
            simpa using lengthEq
          have currentEq : currentControl state = control :=
            currentControl_eq_head state control controls padding
              (by simpa only [List.cons_append] using controlsEq)
          have countPositive : controlCount ≠ 0 := by
            intro countZero
            subst controlCount
            have vectorLength := state.controls.toList_length
            rw [controlsEq] at vectorLength
            simp at vectorLength
          have advancedControls :
              (advance state).controls.toList =
                controls ++ (padding ++ [false]) := by
            rw [advance_controls_toList_of_ne_zero state countPositive,
              controlsEq]
            simp [List.append_assoc]
          have pairRun := scan_pairTokens amount controlCount state pair
            readingEq
          rw [currentEq] at pairRun
          obtain ⟨finalState, restRun⟩ := induction
            (advance state) controls (padding ++ [false])
            (by simpa [advance_readingControls] using readingEq)
            advancedControls tailLengthEq
          refine ⟨finalState, ?_⟩
          change FiniteStateTransducer.scan
              (transition amount controlCount) state
              (((pairTokens pair ++ encode ⟨pairs⟩).map .right)) = _
          rw [List.map_append]
          simp only [FiniteStateTransducer.scan_append, pairRun, restRun]
          rfl

/-- On exactly aligned controls and pairs, the physical transducer emits the
delimiter encoding of the semantically augmented pairs. -/
theorem output_encoded (amount controlCount : Nat)
    (controls : List Bool) (pairs : List (List Bool × List Bool))
    (controlLength : controls.length = controlCount)
    (pairLength : pairs.length = controls.length) :
    output amount controlCount
        (SeparatedProductEncoding.encode id encode (controls, ⟨pairs⟩)) =
      encode ⟨augmentPairs amount controls pairs⟩ := by
  let stored : List.Vector Bool controlCount :=
    ⟨controls, by simpa using controlLength⟩
  have controlsRun := scan_left_initial amount controlCount controls
    controlLength
  have separatorRun :
      FiniteStateTransducer.scan (transition amount controlCount)
          ⟨stored, true⟩ [.separator] =
        (⟨stored, false⟩, []) := by
    rfl
  have storedControls : stored.toList = controls ++ [] := by
    simp [stored]
  obtain ⟨finalState, pairsRun⟩ := scan_pairs amount controlCount
    ⟨stored, false⟩ controls [] pairs rfl storedControls pairLength.symm
  unfold output FiniteStateTransducer.output
    SeparatedProductEncoding.encode
  simp only [id_eq, finish, List.append_nil]
  change
    (FiniteStateTransducer.scan (transition amount controlCount)
      (initialState controlCount)
      (controls.map .left ++ ([.separator] ++
        (encode ⟨pairs⟩).map .right))).2 = _
  rw [FiniteStateTransducer.scan_append, controlsRun]
  simp only [List.nil_append]
  rw [FiniteStateTransducer.scan_append, separatorRun]
  simp only [List.nil_append]
  rw [pairsRun]

end DelimitedBinaryWordPairFixedControlAugmenter
end LeanTrominoes

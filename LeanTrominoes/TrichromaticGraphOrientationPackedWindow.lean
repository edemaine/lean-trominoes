/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationLineWindow
import LeanTrominoes.TrichromaticGraphOrientationFlatEncoding
import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Packed orientation windows have linear binary size -/
namespace LeanTrominoes.TrichromaticGraphOrientation.LineWindow

def decodeWord (input : Input) (word : Nat) : Window input :=
  fun column edge => word.testBit (finProdFinEquiv (column,edge)).val

def encodeWindow (input : Input) (window : Window input) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun index : Fin (3*input.2.length) =>
    window (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)).toNat

theorem decodeWord_encodeWindow (input : Input) (window : Window input) :
    decodeWord input (encodeWindow input window) = window := by
  funext column edge
  simp only [decodeWord,encodeWindow,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  rw [dif_pos (finProdFinEquiv (column,edge)).isLt]
  change window (finProdFinEquiv.symm (finProdFinEquiv (column,edge))).1
    (finProdFinEquiv.symm (finProdFinEquiv (column,edge))).2 = window column edge
  rw [Equiv.symm_apply_apply]

theorem encodeWindow_lt (input : Input) (window : Window input) :
    encodeWindow input window < 2^(3*input.2.length) := by
  simpa only [encodeWindow,List.length_ofFn] using
    (BitVec.ofBoolListLE (List.ofFn fun index : Fin (3*input.2.length) =>
      window (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)).isLt

def packedTransition (input : Input) (first second : Nat) : Prop :=
  LocalWindow.Transition (Valid input) (decodeWord input first) (decodeWord input second)

abbrev PackedState (input : Input) := Fin (2^(3*input.2.length))

theorem hasOrientation_iff_packed_cycle (input : Input) (horizontal : IsOneDimensional input)
    (locality : IsLocal input) : HasOrientation input ↔
    FiniteState.HasCycle (fun first second : PackedState input => packedTransition input first.val second.val) := by
  rw [hasOrientation_iff_cycle input horizontal locality]
  constructor
  · rintro ⟨period,states,steps⟩
    refine ⟨period,fun index => ⟨encodeWindow input (states index),encodeWindow_lt input (states index)⟩,?_⟩
    intro index
    simpa only [packedTransition,decodeWord_encodeWindow] using steps index
  · rintro ⟨period,states,steps⟩
    exact ⟨period,fun index => decodeWord input (states index).val,steps⟩

theorem stateBits_le_input_length (input : Input) :
    3*input.2.length ≤ (FlatEncoding.finEncoding.encode input).length := by
  have fieldsBound := Turing.PartrecToTM2.list_length_le_encodedListSpace (FlatEncoding.fields input)
  have fieldLength := FlatEncoding.fields_length input
  have encoded := PeriodicCNFFlatEncoding.encodeNatFields_length (FlatEncoding.fields input)
  rw [← Turing.PartrecToTM2.encodedListSpace_eq_sum] at encoded
  change 3*input.2.length ≤ (PeriodicCNFFlatEncoding.encodeNatFields (FlatEncoding.fields input)).length
  omega

end LeanTrominoes.TrichromaticGraphOrientation.LineWindow

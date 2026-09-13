/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivitySearch
import LeanTrominoes.IndexedSavitch
import Mathlib.Data.BitVec

/-! # Streaming binary-mask search for a disconnectedness cut

A candidate mask has one bit per input cell. The search does not allocate
the powerset or the list of masks. Machine-space bounds are separate.
-/

namespace LeanTrominoes.PolyominoConnectivitySearch

def maskPart (input : List Cell) (word : Nat) : List Cell :=
  input.filter fun c => word.testBit (input.idxOf c)

def encodePart (input part : List Cell) : Nat :=
  (BitVec.ofBoolListLE (input.map fun c => decide (c ∈ part))).toNat

theorem encodePart_lt (input part : List Cell) : encodePart input part < 2^input.length := by
  simpa [encodePart] using (BitVec.ofBoolListLE (input.map fun c => decide (c ∈ part))).isLt

theorem mem_maskPart_encodePart (input part : List Cell) (c : Cell) :
    c ∈ maskPart input (encodePart input part) ↔ c ∈ input ∧ c ∈ part := by
  simp only [maskPart,List.mem_filter]
  by_cases hc : c ∈ input
  · simp only [hc,true_and,encodePart,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_idxOf hc]
    simp
  · simp [hc]

theorem maskPart_length_le (input : List Cell) (word : Nat) :
    (maskPart input word).length ≤ input.length := List.length_filter_le _ _

def cutCheck (input : List Cell) (word : Nat) : Bool := decide (Cut input (maskPart input word))

def disconnectedPacked (input : List Cell) : Bool :=
  FiniteState.boundedAny (cutCheck input) (2^input.length)

theorem disconnectedPacked_correct (input : List Cell) (nonempty : input ≠ []) :
    disconnectedPacked input = true ↔ ¬ Polyomino.IsConnected input.toFinset := by
  rw [disconnectedPacked,FiniteState.boundedAny_eq_true_iff]
  constructor
  · rintro ⟨word,_,h⟩
    exact not_connected_of_cut input (maskPart input word) (of_decide_eq_true h)
  · intro disconnected
    obtain ⟨part,_,cut⟩ := disconnected_of_not_connected input nonempty disconnected
    refine ⟨encodePart input part,encodePart_lt input part,?_⟩
    apply decide_eq_true
    obtain ⟨⟨a,ha,hap⟩,⟨b,hb,hbp⟩,closed⟩ := cut
    refine ⟨⟨a,ha,(mem_maskPart_encodePart input part a).mpr ⟨ha,hap⟩⟩,
      ⟨b,hb,?_⟩,?_⟩
    · intro h
      exact hbp ((mem_maskPart_encodePart input part b).mp h).2
    · intro u hu v hv edge
      have hup := ((mem_maskPart_encodePart input part u).mp hu).2
      exact (mem_maskPart_encodePart input part v).mpr ⟨hv,closed u hup v hv edge⟩

end LeanTrominoes.PolyominoConnectivitySearch

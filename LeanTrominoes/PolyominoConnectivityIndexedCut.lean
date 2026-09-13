/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivityPacked

/-! # Cuts labelled by input-cell indices, including duplicate cells -/

namespace LeanTrominoes.PolyominoConnectivitySearch

def IndexedCut (input : List Cell) (word : Nat) : Prop :=
  (∃ i < input.length, word.testBit i = true) ∧
  (∃ i < input.length, word.testBit i = false) ∧
  ∀ i (hi : i < input.length), ∀ j (hj : j < input.length),
    word.testBit i = true → (input[i] = input[j] ∨ Cell.SideAdjacent input[i] input[j]) →
      word.testBit j = true

theorem indexedCut_not_connected (input : List Cell) (word : Nat) (cut : IndexedCut input word) :
    ¬ Polyomino.IsConnected input.toFinset := by
  classical
  let part := input.filter fun c => decide (∃ i, ∃ hi : i < input.length, input[i] = c ∧ word.testBit i = true)
  have member (c : Cell) : c ∈ part ↔ c ∈ input ∧ ∃ i, ∃ hi : i < input.length, input[i] = c ∧ word.testBit i = true := by
    simp [part]
  obtain ⟨⟨i,hi,bi⟩,⟨j,hj,bj⟩,closed⟩ := cut
  apply not_connected_of_cut input part
  refine ⟨⟨input[i],List.getElem_mem hi,(member _).mpr ⟨List.getElem_mem hi,i,hi,rfl,bi⟩⟩,
    ⟨input[j],List.getElem_mem hj,?_⟩,?_⟩
  · intro h
    obtain ⟨_,k,hk,eq,bk⟩ := (member _).mp h
    have bad := closed k hk j hj bk (Or.inl eq)
    simp [bj] at bad
  · intro a ha b hb edge
    obtain ⟨_,k,hk,eq,bk⟩ := (member _).mp ha
    obtain ⟨l,hl,eqb⟩ := List.mem_iff_getElem.mp hb
    have bl := closed k hk l hl bk (Or.inr (by simpa [eq,eqb] using edge))
    exact (member _).mpr ⟨hb,l,hl,eqb,bl⟩

theorem testBit_encodePart (input part : List Cell) (i : Nat) (hi : i < input.length) :
    (encodePart input part).testBit i = decide (input[i] ∈ part) := by
  simp [encodePart,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi]

theorem indexedCut_encodePart (input part : List Cell) (cut : Cut input part) :
    IndexedCut input (encodePart input part) := by
  obtain ⟨⟨a,ha,hap⟩,⟨b,hb,hbp⟩,closed⟩ := cut
  obtain ⟨i,hi,eqi⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j,hj,eqj⟩ := List.mem_iff_getElem.mp hb
  refine ⟨⟨i,hi,?_⟩,⟨j,hj,?_⟩,?_⟩
  · rw [testBit_encodePart _ _ _ hi,eqi]
    exact decide_eq_true hap
  · rw [testBit_encodePart _ _ _ hj,eqj]
    exact decide_eq_false hbp
  · intro k hk l hl bit edge
    rw [testBit_encodePart _ _ _ hk,decide_eq_true_eq] at bit
    rw [testBit_encodePart _ _ _ hl,decide_eq_true_eq]
    rcases edge with eq | edge
    · simpa [← eq] using bit
    · exact closed _ bit _ (List.getElem_mem hl) edge

theorem exists_indexedCut_iff (input : List Cell) (nonempty : input ≠ []) :
    (∃ word < 2^input.length, IndexedCut input word) ↔ ¬ Polyomino.IsConnected input.toFinset := by
  constructor
  · rintro ⟨word,_,cut⟩
    exact indexedCut_not_connected input word cut
  · intro h
    obtain ⟨part,_,cut⟩ := disconnected_of_not_connected input nonempty h
    exact ⟨encodePart input part,encodePart_lt input part,indexedCut_encodePart input part cut⟩

end LeanTrominoes.PolyominoConnectivitySearch

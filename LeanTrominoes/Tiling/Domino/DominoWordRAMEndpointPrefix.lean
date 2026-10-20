/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointCandidate

/-! # Prefix invariants for the constructed endpoint arrays -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter

/-- The first records of two physical endpoint arrays. -/
def Prefix (data : Data) (left right : ℕ) (words : List (ℕ × ℕ)) : Prop :=
  ∀ i, ∀ within : i< words.length, data.2 (left+i)=words[i].1 ∧ data.2 (right+i)=words[i].2

theorem appendMemory_append (memory : ℕ → ℕ) (left right index : ℕ) (first second : List (ℕ × ℕ)) :
    appendMemory memory left right index (first++second)=
      appendMemory (appendMemory memory left right index first) left right (index+first.length) second := by
  induction first generalizing memory index with
  | nil => simp [appendMemory]
  | cons pair rest ih => simpa [appendMemory,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (ih (writeMemory memory left right index pair.1 pair.2) (index+1))

theorem Output.trans {first second : List (ℕ × ℕ)} {before middle after : Data}
    (a : Output first before middle) (b : Output second middle after) : Output (first++second) before after := by
  constructor
  · rw [b.memory,a.memory,a.fixed H.left (by decide) (by decide),a.fixed H.right (by decide) (by decide),a.index]
    exact (appendMemory_append _ _ _ _ first second).symm
  · rw [b.index,a.index,List.length_append]
    omega
  · intro reg low different
    exact (b.fixed reg low different).trans (a.fixed reg low different)

theorem Output.refl (data : Data) : Output [] data data := ⟨rfl,by simp,fun _ _ _ => rfl⟩

theorem Prefix.empty (data : Data) (left right : ℕ) : Prefix data left right [] := by simp [Prefix]

theorem Prefix.transport {before after : Data} {left right : ℕ} {words : List (ℕ × ℕ)}
    (h : Prefix before left right words)
    (memory : ∀ address, (left≤ address ∧ address< left+words.length) ∨
      (right≤ address ∧ address< right+words.length) → after.2 address=before.2 address) :
    Prefix after left right words := by
  intro i within
  rw [memory (left+i) (Or.inl (by omega)),memory (right+i) (Or.inr (by omega))]
  exact h i within

theorem Prefix.transport_below {before after : Data} {left right frontier parities dimension : ℕ}
    {words : List (ℕ × ℕ)} (h : Prefix before left right words)
    (leftBelow : left+words.length≤ frontier) (rightBelow : right+words.length≤ frontier)
    (leftAway : left+words.length≤ parities ∨ parities+dimension≤ left)
    (rightAway : right+words.length≤ parities ∨ parities+dimension≤ right)
    (memory : ∀ address, address< frontier → (address< parities ∨ parities+dimension≤ address) →
      after.2 address=before.2 address) : Prefix after left right words := by
  apply h.transport
  intro address within
  rcases within with leftMember | rightMember
  · apply memory address (by omega)
    rcases leftAway with before | after <;> omega
  · apply memory address (by omega)
    rcases rightAway with before | after <;> omega

theorem appendMemory_get (memory : ℕ → ℕ) (left right capacity index : ℕ) (words : List (ℕ × ℕ))
    (adjacent : right=left+capacity) (within : index+words.length≤ capacity) :
    ∀ i, ∀ hi : i< words.length,
      appendMemory memory left right index words (left+index+i)=words[i].1 ∧
      appendMemory memory left right index words (right+index+i)=words[i].2 := by
  induction words generalizing memory index with
  | nil => simp
  | cons pair rest ih =>
    intro i hi
    cases i with
    | zero =>
      have cap : 0< capacity := by simp only [List.length_cons] at within; omega
      have leftDifferent : left+index≠right+index := by omega
      have leftFrame := appendMemory_frame (writeMemory memory left right index pair.1 pair.2) left right (index+1) rest (left+index)
        (Or.inl (by omega)) (Or.inl (by omega))
      have rightFrame := appendMemory_frame (writeMemory memory left right index pair.1 pair.2) left right (index+1) rest (right+index)
        (Or.inr (by simp only [List.length_cons] at within; omega)) (Or.inl (by omega))
      simp only [Nat.add_zero,List.getElem_cons_zero,appendMemory]
      constructor
      · rw [leftFrame]
        simp only [writeMemory,Function.update_of_ne leftDifferent,Function.update_self]
      · rw [rightFrame]
        simp only [writeMemory,Function.update_self]
    | succ i =>
      have rest := ih (writeMemory memory left right index pair.1 pair.2) (index+1) (by simp only [List.length_cons] at within; omega)
        i (by simp only [List.length_cons] at hi; omega)
      simpa only [appendMemory,Nat.add_assoc,Nat.add_comm 1 i,List.getElem_cons_succ] using rest

theorem Output.prefix_append {old words : List (ℕ × ℕ)} {before after : Data} {left right capacity : ℕ}
    (h : Output words before after) (previous : Prefix before left right old)
    (left_eq : before.1 H.left=left) (right_eq : before.1 H.right=right) (index_eq : before.1 H.index=old.length)
    (adjacent : right=left+capacity) (within : old.length+words.length≤ capacity) :
    Prefix after left right (old++words) := by
  intro i hi
  by_cases prior : i< old.length
  · have leftOutside : left+i< left+old.length := by omega
    have rightOutside : right+i< right+old.length := by omega
    have leftFrame := h.frame (left+i) (by rw [left_eq,index_eq]; exact Or.inl leftOutside)
      (by rw [right_eq,index_eq]; exact Or.inl (by omega))
    have rightFrame := h.frame (right+i) (by rw [left_eq,index_eq]; exact Or.inr (by omega))
      (by rw [right_eq,index_eq]; exact Or.inl rightOutside)
    rw [leftFrame,rightFrame,List.getElem_append_left prior]
    exact previous i prior
  · have offset : i-old.length< words.length := by rw [List.length_append] at hi; omega
    have read := appendMemory_get before.2 left right capacity old.length words adjacent within (i-old.length) offset
    rw [h.memory,left_eq,right_eq,index_eq]
    have index : old.length+(i-old.length)=i := Nat.add_sub_of_le (by omega)
    simpa only [Nat.add_assoc,index,List.getElem_append_right (by omega : old.length≤ i)] using read

end LeanTrominoes.Domino.WordRAM.EndpointWriter

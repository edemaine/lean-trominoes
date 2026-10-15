/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-! # Local cell constraints for a bounded binary certificate -/
namespace LeanTrominoes.FiniteCertificate
variable {Alphabet : Type*}

def CellAllowed (initial : List Alphabet) (bit : Bool → Alphabet) (capacity index : Nat)
    (cell : Option Alphabet) : Prop :=
  if index < initial.length then cell=initial[index]?
  else if index < initial.length+capacity then cell=none ∨ ∃ b, cell=some (bit b)
  else cell=none

theorem exists_map_of_mem (bit : Bool → Alphabet) (word : List Alphabet)
    (h : ∀ symbol∈word, ∃ b, symbol=bit b) :
    ∃ certificate : List Bool, word=certificate.map bit := by
  induction word with
  | nil => exact ⟨[],rfl⟩
  | cons symbol rest ih =>
    obtain ⟨b,rfl⟩ := h symbol (by simp)
    obtain ⟨tail,ht⟩ := ih (fun a ha => h a (by simp [ha]))
    exact ⟨b::tail,by simp [ht]⟩

theorem cellAllowed_iff (initial : List Alphabet) (bit : Bool → Alphabet)
    (capacity : Nat) (word : List Alphabet) :
    (∀ index, CellAllowed initial bit capacity index word[index]?) ↔
      ∃ certificate : List Bool, certificate.length ≤ capacity ∧ word=initial++certificate.map bit := by
  constructor
  · intro cells
    have lengthBound : word.length ≤ initial.length+capacity := by
      have h := cells (initial.length+capacity)
      simp only [CellAllowed,show ¬initial.length+capacity < initial.length by omega,
        if_false,lt_self_iff_false] at h
      exact List.getElem?_eq_none_iff.mp h
    have takeEq : word.take initial.length=initial := by
      apply List.ext_getElem?
      intro index
      by_cases inside : index < initial.length
      · simpa [CellAllowed,List.getElem?_take,inside] using cells index
      · simp [inside]
    have suffixBits : ∀ symbol∈word.drop initial.length, ∃ b, symbol=bit b := by
      intro symbol member
      obtain ⟨index,hi,heq⟩ := List.getElem_of_mem member
      have lookup : word[initial.length+index]?=some symbol := by
        simpa [List.getElem?_drop] using (List.getElem?_eq_getElem hi).trans (congrArg some heq)
      have h := cells (initial.length+index)
      have indexBound : initial.length+index < initial.length+capacity := by
        simp only [List.length_drop] at hi
        omega
      simp only [CellAllowed,show ¬initial.length+index < initial.length by omega,
        if_false,if_pos indexBound,lookup,Option.some_ne_none,false_or,Option.some.injEq] at h
      exact h
    obtain ⟨certificate,hc⟩ := exists_map_of_mem bit (word.drop initial.length) suffixBits
    refine ⟨certificate,?_,?_⟩
    · have lengths := congrArg List.length hc
      simp only [List.length_drop,List.length_map] at lengths
      omega
    · simpa only [takeEq,hc] using (List.take_append_drop initial.length word).symm
  · rintro ⟨certificate,bound,rfl⟩ index
    by_cases before : index < initial.length
    · simp [CellAllowed,before,List.getElem?_append]
    · by_cases inside : index < initial.length+capacity
      · simp only [CellAllowed,if_pos inside,List.getElem?_append,if_neg before,List.getElem?_map]
        cases h : certificate[index-initial.length]? with
        | none => simp
        | some b => exact Or.inr ⟨b,rfl⟩
      · simp only [CellAllowed,if_neg before,if_neg inside]
        apply List.getElem?_eq_none
        simp only [List.length_append,List.length_map]
        omega

theorem bounded_cellAllowed_iff (initial : List Alphabet) (bit : Bool → Alphabet)
    (capacity space : Nat) (word : List Alphabet)
    (fits : word.length ≤ space) (room : initial.length+capacity ≤ space) :
    (∀ index : Fin space, CellAllowed initial bit capacity index.val word[index.val]?) ↔
      ∃ certificate : List Bool, certificate.length ≤ capacity ∧ word=initial++certificate.map bit := by
  rw [← cellAllowed_iff]
  constructor
  · intro cells index
    by_cases inside : index < space
    · exact cells ⟨index,inside⟩
    · simp [CellAllowed,show ¬index < initial.length by omega,
        show ¬index < initial.length+capacity by omega,List.getElem?_eq_none (by omega : word.length ≤ index)]
  · intro cells index
    exact cells index.val

end LeanTrominoes.FiniteCertificate

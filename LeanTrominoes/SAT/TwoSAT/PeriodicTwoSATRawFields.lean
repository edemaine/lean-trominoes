/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATRawInput

/-! # Field lookup in original fixed-size clause records -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw
variable {n d : ℕ}

def validFlag : Clause (Fin n) d → ℤ
  | none => 0
  | some _ => 1

def firstVariable : Clause (Fin n) d → ℤ
  | none => 0
  | some (a,_) => a.1.1.val

def secondVariable : Clause (Fin n) d → ℤ
  | none => 0
  | some (_,b) => b.1.1.val

def firstSign : Clause (Fin n) d → ℤ
  | none => 0
  | some (a,_) => if a.1.2 then 1 else 0

def secondSign : Clause (Fin n) d → ℤ
  | none => 0
  | some (_,b) => if b.1.2 then 1 else 0

def firstOffset : Clause (Fin n) d → Fin d → ℤ
  | none => fun _ => 0
  | some (a,_) => a.2

def secondOffset : Clause (Fin n) d → Fin d → ℤ
  | none => fun _ => 0
  | some (_,b) => b.2

theorem flag_word (c : Clause (Fin n) d) : (clauseWords c)[0]?=some (validFlag c) := by
  cases c with
  | none => simp [clauseWords,recordSize,validFlag]
  | some pair => rcases pair with ⟨a,b⟩; simp [clauseWords,validFlag]

theorem firstVariable_word (c : Clause (Fin n) d) : (clauseWords c)[1]?=some (firstVariable c) := by
  cases c with
  | none =>
    simp only [clauseWords,recordSize,firstVariable]
    exact List.getElem?_replicate_of_lt (by omega)
  | some pair => rcases pair with ⟨a,b⟩; simp [clauseWords,firstVariable]

theorem secondVariable_word (c : Clause (Fin n) d) : (clauseWords c)[3]?=some (secondVariable c) := by
  cases c with
  | none =>
    simp only [clauseWords,recordSize,secondVariable]
    exact List.getElem?_replicate_of_lt (by omega)
  | some pair => rcases pair with ⟨a,b⟩; simp [clauseWords,secondVariable]

theorem firstSign_word (c : Clause (Fin n) d) : (clauseWords c)[2]?=some (firstSign c) := by
  cases c with
  | none =>
    simp only [clauseWords,recordSize,firstSign]
    exact List.getElem?_replicate_of_lt (by omega)
  | some pair => rcases pair with ⟨a,b⟩; simp [clauseWords,firstSign]

theorem secondSign_word (c : Clause (Fin n) d) : (clauseWords c)[4]?=some (secondSign c) := by
  cases c with
  | none =>
    simp only [clauseWords,recordSize,secondSign]
    exact List.getElem?_replicate_of_lt (by omega)
  | some pair => rcases pair with ⟨a,b⟩; simp [clauseWords,secondSign]

theorem firstOffset_word (c : Clause (Fin n) d) (j : Fin d) :
    (clauseWords c)[5+j.val]?=some (firstOffset c j) := by
  cases c with
  | none =>
    simp only [clauseWords,firstOffset,List.getElem?_replicate]
    split_ifs with within
    · rfl
    · exact False.elim (within (by dsimp [recordSize]; omega))
  | some pair =>
    rcases pair with ⟨a,b⟩
    simp only [clauseWords,firstOffset]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_append_right (by simp <;> omega)]
    simp only [List.length_cons,List.length_nil]
    have index : 5+j.val-(0+1+1+1+1+1)=j.val := by omega
    rw [index]
    rw [List.getElem?_eq_getElem (by simp)]
    simp

theorem secondOffset_word (c : Clause (Fin n) d) (j : Fin d) :
    (clauseWords c)[5+d+j.val]?=some (secondOffset c j) := by
  cases c with
  | none =>
    simp only [clauseWords,secondOffset,List.getElem?_replicate]
    split_ifs with within
    · rfl
    · exact False.elim (within (by dsimp [recordSize]; omega))
  | some pair =>
    rcases pair with ⟨a,b⟩
    simp only [clauseWords,secondOffset]
    rw [List.getElem?_append_right (by simp <;> omega)]
    simp only [List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_finRange]
    have index : 5+d+j.val-(0+1+1+1+1+1+d)=j.val := by omega
    rw [index]
    rw [List.getElem?_eq_getElem (by simp)]
    simp

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw

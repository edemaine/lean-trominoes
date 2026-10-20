/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATNormalization
import LeanTrominoes.ComplexityAbstract

/-! # The original clause encoding for the periodic word-RAM solver

The input contains only the variable/clause counts and fixed-size clause
records. Each nonempty record has its two variable indices, two sign bits, and
both original coordinate vectors. A final zero record permits harmless bounded
loads in inactive arithmetic alternatives. Common offsets are retained. No normalized
differences, cover, Horn table, occurrence index, or answer is supplied.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw
variable {n d : ℕ}

abbrev Input (d : ℕ) := Σ n : ℕ, Formula (Fin n) d
abbrev LocalInput (d : ℕ) := {input : Input d // LocalDifferences input.2}

def recordSize (d : ℕ) : ℕ := 5+2*d

def clauseWords : Clause (Fin n) d → List ℤ
  | none => List.replicate (recordSize d) 0
  | some (a,b) => [(1:ℤ),(a.1.1.val:ℤ),(if a.1.2 then 1 else 0),(b.1.1.val:ℤ),(if b.1.2 then 1 else 0)] ++
      (List.finRange d).map a.2 ++ (List.finRange d).map b.2

def records (input : Input d) : List (Clause (Fin input.1) d) := input.2++[none]

def words (input : Input d) : List ℤ :=
  [(input.1:ℤ),(input.2.length:ℤ)]++(records input).flatMap clauseWords

def encode (input : LocalInput d) : List ℤ := words input.val

def size (input : LocalInput d) : ℕ := input.val.1+input.val.2.length+1

def Satisfiable (input : LocalInput d) : Prop := PeriodicTwoSAT.Satisfiable input.val.2

theorem clauseWords_length (c : Clause (Fin n) d) : (clauseWords c).length=recordSize d := by
  cases c with
  | none => simp [clauseWords]
  | some pair => rcases pair with ⟨a,b⟩; simp [clauseWords,recordSize]; omega

theorem words_length (input : Input d) :
    (words input).length=2+recordSize d*(input.2.length+1) := by
  simp only [words,records,List.length_append,List.length_cons,List.length_nil,List.length_flatMap,clauseWords_length]
  simp [Nat.mul_comm,Nat.mul_add]

theorem fixedBlock_get {V W : Type} (xs : List V) (block : V → List W) (width : ℕ)
    (lengths : ∀ a, (block a).length=width) (i : ℕ) (within : i<xs.length)
    (j : ℕ) (inside : j<width) :
    (xs.flatMap block)[i*width+j]?=(block xs[i])[j]? := by
  induction xs generalizing i with
  | nil => simp at within
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      exact List.getElem?_append_left (by rw [lengths]; exact inside)
    | succ i =>
      have next : i<xs.length := by simpa using within
      rw [List.flatMap_cons,List.getElem?_append_right (by rw [lengths,Nat.add_mul]; omega)]
      have index : (i+1)*width+j-(block a).length=i*width+j := by rw [lengths,Nat.add_mul]; omega
      rw [index]
      exact ih i next

theorem clause_word (input : Input d) (i : ℕ) (within : i< input.2.length)
    (j : ℕ) (inside : j<recordSize d) :
    (words input)[2+i*recordSize d+j]?=(clauseWords input.2[i])[j]? := by
  simp only [words]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  have index : 2+i*recordSize d+j-2=i*recordSize d+j := by omega
  rw [index]
  have eq := fixedBlock_get (records input) clauseWords (recordSize d) clauseWords_length i
    (by simp [records]; omega) j inside
  simpa only [records,List.getElem_append_left within] using eq

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Raw

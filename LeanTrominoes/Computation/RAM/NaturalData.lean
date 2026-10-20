/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Arrays

/-! # Natural-valued states in bounded-word program proofs

This is a proof view of the existing RAM, not an instruction set extension.
Each lemma produces an execution of the displayed ordinary instructions and
checks the written words and addresses. Subtraction requires a nonnegative
result. The Horn program uses only natural-valued input and intermediate data.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM

abbrev NaturalData (r : ℕ) := (Fin r → ℕ) × (ℕ → ℕ)

namespace NaturalData

def word {r : ℕ} (data : NaturalData r) : Data r :=
  (fun i => (data.1 i : ℤ), fun a => (data.2 a : ℤ))

def set {r : ℕ} (data : NaturalData r) (i : Fin r) (value : ℕ) : NaturalData r :=
  (Function.update data.1 i value,data.2)

def store {r : ℕ} (data : NaturalData r) (address value : ℕ) : NaturalData r :=
  (data.1,Function.update data.2 address value)

theorem cast_update {I : Type} [DecidableEq I] (f : I → ℕ) (i : I) (n : ℕ) :
    (fun j => (Function.update f i n j : ℤ))=Function.update (fun j => (f j : ℤ)) i n := by
  funext j
  simp only [Function.update_apply]
  split <;> rfl

theorem word_set {r : ℕ} (data : NaturalData r) (i : Fin r) (n : ℕ) :
    (data.set i n).word=(Function.update data.word.1 i n,data.word.2) := by
  simp only [set,word,cast_update]

theorem word_store {r : ℕ} (data : NaturalData r) (address value : ℕ) :
    (data.store address value).word=(data.word.1,Function.update data.word.2 address value) := by
  simp only [store,word,cast_update]

/-- A single natural bound controls all register and memory words. -/
def Bounded {r : ℕ} (bound : ℕ) (data : NaturalData r) : Prop :=
  (∀ i, data.1 i≤bound) ∧ ∀ address, data.2 address≤bound

theorem Bounded.mono {r a b : ℕ} {data : NaturalData r} (h : Bounded a data) (le : a≤b) :
    Bounded b data := ⟨fun i => (h.1 i).trans le,fun address => (h.2 address).trans le⟩

theorem Bounded.set {r bound n : ℕ} {data : NaturalData r} (h : Bounded bound data)
    (i : Fin r) (value : n≤bound) : Bounded bound (data.set i n) := by
  constructor
  · intro j
    simp only [NaturalData.set,Function.update_apply]
    split
    · exact value
    · exact h.1 j
  · exact h.2

theorem Bounded.store {r bound address n : ℕ} {data : NaturalData r} (h : Bounded bound data)
    (value : n≤bound) : Bounded bound (data.store address n) := by
  constructor
  · exact h.1
  · intro a
    simp only [NaturalData.store,Function.update_apply]
    split
    · exact value
    · exact h.2 a

/-- This abbreviation retains the original structured program and its exact
primitive instruction count. -/
abbrev Exec {r : ℕ} (w : ℕ) (code : Structured.Code r) (before after : NaturalData r) (cost : ℕ) :=
  Structured.Exec w code before.word after.word cost

theorem constant_exec {r w : ℕ} (data : NaturalData r) (dst : Fin r) (n : ℕ)
    (fits : Fits w n) : Exec w (.atom (.constant dst n)) data (data.set dst n) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  simp [Structured.Primitive.eval,fits]

theorem copy_exec {r w : ℕ} (data : NaturalData r) (dst src : Fin r)
    (fits : Fits w (data.1 src)) : Exec w (.atom (.copy dst src)) data (data.set dst (data.1 src)) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  simp [Structured.Primitive.eval,word,fits]

theorem add_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (fits : Fits w (data.1 left+data.1 right : ℕ)) :
    Exec w (.atom (.arithmetic .add dst left right)) data (data.set dst (data.1 left+data.1 right)) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  simp only [Nat.cast_add] at fits
  simp [Structured.Primitive.eval,Arithmetic.eval,word,fits]

theorem sub_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (nonnegative : data.1 right≤data.1 left) (fits : Fits w (data.1 left-data.1 right : ℕ)) :
    Exec w (.atom (.arithmetic .sub dst left right)) data (data.set dst (data.1 left-data.1 right)) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  have cast : ((data.1 left-data.1 right : ℕ) : ℤ)=(data.1 left : ℤ)-data.1 right :=
    Int.ofNat_sub nonnegative
  rw [cast] at fits
  simp [Structured.Primitive.eval,Arithmetic.eval,word,fits,cast]

theorem load_exec {r w : ℕ} (data : NaturalData r) (dst address : Fin r)
    (addressFits : Fits w (data.1 address)) (valueFits : Fits w (data.2 (data.1 address))) :
    Exec w (.atom (.load dst address)) data (data.set dst (data.2 (data.1 address))) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  have valid : ¬((data.1 address : ℤ)<0 ∨ (data.1 address : ℤ)≥(2^w : ℕ)) := by
    push Not
    exact ⟨Int.natCast_nonneg _,Allocation.nat_address addressFits⟩
  simp only [Structured.Primitive.eval,word,valid,ite_false,Int.toNat_natCast,valueFits,ite_true]

theorem store_exec {r w : ℕ} (data : NaturalData r) (address src : Fin r)
    (addressFits : Fits w (data.1 address)) (valueFits : Fits w (data.1 src)) :
    Exec w (.atom (.store address src)) data (data.store (data.1 address) (data.1 src)) 1 := by
  rw [Exec,word_store]
  apply Structured.Exec.atom
  have valid : ¬((data.1 address : ℤ)<0 ∨ (data.1 address : ℤ)≥(2^w : ℕ) ∨ ¬Fits w (data.1 src)) := by
    push Not
    exact ⟨Int.natCast_nonneg _,Allocation.nat_address addressFits,valueFits⟩
  simp only [Structured.Primitive.eval,word,valid,ite_false,Int.toNat_natCast]

theorem read_exec {r w : ℕ} (data : NaturalData r) (scratch dst pointer index : Fin r)
    (addressFits : Fits w (data.1 pointer+data.1 index : ℕ))
    (valueFits : Fits w (data.2 (data.1 pointer+data.1 index))) :
    Exec w (Allocation.readProgram scratch dst pointer index) data
      ((data.set scratch (data.1 pointer+data.1 index)).set dst
        (data.2 (data.1 pointer+data.1 index))) 2 := by
  have first := add_exec data scratch pointer index addressFits
  have second := load_exec (data.set scratch (data.1 pointer+data.1 index)) dst scratch
    (by simpa [set] using addressFits) (by simpa [set] using valueFits)
  simpa only [Exec,Allocation.readProgram,set,Function.update_self,Nat.reduceAdd] using first.seq second

theorem write_exec {r w : ℕ} (data : NaturalData r) (scratch src pointer index : Fin r)
    (different : src≠scratch) (addressFits : Fits w (data.1 pointer+data.1 index : ℕ))
    (valueFits : Fits w (data.1 src)) :
    Exec w (Allocation.writeProgram scratch src pointer index) data
      ((data.set scratch (data.1 pointer+data.1 index)).store
        (data.1 pointer+data.1 index) (data.1 src)) 2 := by
  have first := add_exec data scratch pointer index addressFits
  have second := store_exec (data.set scratch (data.1 pointer+data.1 index)) scratch src
    (by simpa [set] using addressFits) (by simpa [set,different] using valueFits)
  simpa [Exec,Allocation.writeProgram,set,store,different] using first.seq second

end NaturalData
end LeanTrominoes.ComplexityAbstract.RAM

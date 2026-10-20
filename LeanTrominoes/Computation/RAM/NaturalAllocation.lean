/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalData

/-! # Allocation certificates for natural-valued program states

The statements here re-express the already verified allocation macro. They do
not add an allocation instruction or alter its primitive instruction cost.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.NaturalData

def clear (memory : ℕ → ℕ) (base : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => memory
  | n+1 => clear (Function.update memory base 0) (base+1) n

theorem clear_word (memory : ℕ → ℕ) (base count : ℕ) :
    (fun address => (clear memory base count address : ℤ))=
      Allocation.clear (fun address => (memory address : ℤ)) base count := by
  induction count generalizing memory base with
  | zero => rfl
  | succ n ih =>
    simp only [clear,Allocation.clear]
    rw [ih,cast_update]
    simp only [Nat.cast_zero]

def allocatedRegisters {r : ℕ} (frame : Fin (r+6) → ℕ) (endAddress length pointer : ℕ) :
    Fin (r+6) → ℕ := fun i =>
  if i=Allocation.frontier r then endAddress else
  if i=Allocation.count r then length else
  if i=Allocation.result r then pointer else
  if i=Allocation.cursor r then endAddress else
  if i=Allocation.zero r then 0 else
  if i=Allocation.one r then 1 else frame i

def allocated {r : ℕ} (data : NaturalData (r+6)) (base length : ℕ) : NaturalData (r+6) :=
  (allocatedRegisters data.1 (base+length) length base,clear data.2 base length)

theorem allocated_word {r : ℕ} (data : NaturalData (r+6)) (base length : ℕ) :
    (data.allocated base length).word=
      (Allocation.registers data.word.1 (base+length) length base (base+length),
        Allocation.clear data.word.2 base length) := by
  apply Prod.ext
  · funext i
    simp only [allocated,word,allocatedRegisters,Allocation.registers]
    split_ifs <;> rfl
  · exact clear_word _ _ _

theorem allocate_exec {r w : ℕ} (data : NaturalData (r+6)) (base length : ℕ)
    (front : data.1 (Allocation.frontier r)=base) (request : data.1 (Allocation.count r)=length)
    (width : Fits w (base+length : ℕ)) (unit : Fits w 1) :
    Exec w (Allocation.program r) data (data.allocated base length) (4*length+7) := by
  change Structured.Exec w _ _ _ _
  rw [allocated_word]
  exact Allocation.exec data.word.1 data.word.2 base length
    (by change (data.1 (Allocation.frontier r) : ℤ)=(base : ℤ); rw [front])
    (by change (data.1 (Allocation.count r) : ℤ)=(length : ℤ); rw [request]) width unit

def initialized {r : ℕ} (data : NaturalData (r+6)) (inputLength : ℕ) : NaturalData (r+6) :=
  ((data.set (Allocation.zero r) 0).set (Allocation.one r) 1).set (Allocation.frontier r) (inputLength+1)

theorem initialize_exec {r w : ℕ} (data : NaturalData (r+6)) (inputLength : ℕ)
    (header : data.2 0=inputLength) (width : Fits w (inputLength+1 : ℕ)) (unit : Fits w 1) :
    Exec w (Allocation.initializeProgram r) data (data.initialized inputLength) 4 := by
  have trace := Allocation.initialize_exec data.word.1 data.word.2 inputLength
    (by change (data.2 0 : ℤ)=(inputLength : ℤ); rw [header]) width unit
  simpa only [Exec,initialized,word_set,Nat.cast_zero,Nat.cast_one,Prod.eta] using trace

theorem allocated_bounded {r bound base length : ℕ} {data : NaturalData (r+6)}
    (initial : Bounded bound data) (endpoint : base+length≤bound) (unit : 1≤bound) :
    Bounded bound (data.allocated base length) := by
  constructor
  · intro i
    simp only [allocated,allocatedRegisters]
    split_ifs <;> first | omega | exact initial.1 i
  · intro address
    change clear data.2 base length address≤bound
    have fits := Allocation.clear_apply (fun a => (data.2 a : ℤ)) base length address
    rw [← clear_word] at fits
    dsimp only at fits
    have before := initial.2 address
    split_ifs at fits <;> omega

end LeanTrominoes.ComplexityAbstract.RAM.NaturalData

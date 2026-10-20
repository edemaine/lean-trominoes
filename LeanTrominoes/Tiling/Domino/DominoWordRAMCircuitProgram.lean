/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitMemory

/-! # Execution of fixed binary arithmetic circuits

The node list is compiled into one finite ordinary RAM program. Input slots
precede all output slots, and each instruction refers only to earlier slots.
Unwritten output arrays are zero; their initialization is a caller obligation.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

def Valid : List Node → ℕ → Prop
  | [], _ => True
  | node::rest, start => node.Valid start ∧ Valid rest (start+1)

def evaluate {R : Type} [Ring R] : List Node → ℕ → (ℕ → R) → (ℕ → R)
  | [], _, values => values
  | node::rest, start, values => evaluate rest (start+1) (node.advance start values)

def program : List Node → ℕ → Code
  | [], _ => .atom (.copy baseRegister baseRegister)
  | node::rest, start => .seq (node.program start) (program rest (start+1))

/-- All actual digit loops and pointer computations contribute to this bound. -/
theorem program_exec {w base length slots : ℕ} (nodes : List Node) :
    ∀ start values data, Represents base length start values data →
    Valid nodes start → 0< length → start+nodes.length≤slots →
    (∀ slot, start≤slot → slot< start+nodes.length → ∀ i< length,
      data.2 (slotBase base length slot+i)=0) →
    Fits w (resourceBound base length slots) →
    ∃ result cost, NaturalData.Exec w (program nodes start) data result cost ∧
      cost≤(26*length^2+26*length+16)*nodes.length+1 ∧
      Represents base length (start+nodes.length) (evaluate nodes start values) result ∧
      ∀ address, (address< slotBase base length start ∨ slotBase base length (start+nodes.length)≤address) →
        result.2 address=data.2 address := by
  induction nodes with
  | nil =>
    intro start values data h _ positive capacity zero fits
    have baseFits : Fits w (data.1 baseRegister) := by
      rw [h.base_eq]
      exact Allocation.nat_fits_le fits (by unfold resourceBound; omega)
    have copy := NaturalData.copy_exec data baseRegister baseRegister baseFits
    refine ⟨data,1,?_,by simp,by simpa [evaluate] using h,fun _ _ => rfl⟩
    simpa [program,NaturalData.set] using copy
  | cons node rest ih =>
    intro start values data h valid positive capacity zero fits
    obtain ⟨middle,firstCost,firstRun,firstBound,step⟩ := node_exec node data h.base_eq h.length_eq
      positive (by simp only [List.length_cons] at capacity; omega) valid.1 h.bits
      (zero start (le_refl _) (by simp only [List.length_cons]; omega)) fits
    have next := h.advance valid.1 step
    have future : ∀ slot, start+1≤slot → slot< (start+1)+rest.length → ∀ i< length,
        middle.2 (slotBase base length slot+i)=0 := by
      intro slot later within i hi
      exact step.future_zero zero slot later (by simp only [List.length_cons]; omega) i hi
    obtain ⟨result,restCost,restRun,restBound,correct,frame⟩ := ih (start+1) (node.advance start values)
      middle next valid.2 positive (by simp only [List.length_cons] at capacity; omega) future fits
    refine ⟨result,firstCost+restCost,firstRun.seq restRun,?_,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa only [evaluate,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using correct
    · intro address outside
      have startGrow := slotBase_mono base length (show start≤start+1 by omega)
      have endGrow := slotBase_mono base length (show start+1≤start+(node::rest).length by simp only [List.length_cons]; omega)
      rw [slotBase_succ] at endGrow
      have restOutside : address< slotBase base length (start+1) ∨
          slotBase base length ((start+1)+rest.length)≤address := by
        rcases outside with before | after
        · exact Or.inl (lt_of_lt_of_le before startGrow)
        · exact Or.inr (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using after)
      have firstOutside : address< slotBase base length start ∨ slotBase base length start+length≤address := by
        rcases outside with before | after
        · exact Or.inl before
        · exact Or.inr (endGrow.trans after)
      exact (frame address restOutside).trans (step.frame address firstOutside)

theorem node_program_size (node : Node) (output : ℕ) : (node.program output).size≤136 := by
  cases node with
  | constant bit => simp [Node.program,constantProgram,pointerProgram,Structured.Code.size]
  | arithmetic op first second =>
    have size := operation_size op
    simpa only [Node.program,arithmeticProgram,prepareProgram,pointerProgram,Structured.Code.size,Structured.Code.size_embed] using
      (show 9+op.code.size≤136 by omega)

theorem program_size (nodes : List Node) (start : ℕ) : (program nodes start).size≤136*nodes.length+1 := by
  induction nodes generalizing start with
  | nil => simp [program,Structured.Code.size]
  | cons node rest ih =>
    have first := node_program_size node start
    have later := ih (start+1)
    simp only [program,Structured.Code.size,List.length_cons]
    nlinarith

end LeanTrominoes.Domino.WordRAM.Binary.Circuit

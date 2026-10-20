/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATZero
import LeanTrominoes.Computation.RAM.MemoryFrame
import LeanTrominoes.Computation.RAM.RegisterEmbedding
import LeanTrominoes.SAT.Horn.HornWordRAMLinearTime

/-! # Calling the verified Horn program from a constructed low-memory table

The constructor explicitly clears unused low memory and resets the registers.
The Horn execution is then replayed at the caller's width, preserving its high
input arena and retaining every primitive instruction in the running time.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

/-- The exact width at which the Horn operational certificate is instantiated. -/
def hornWidth (input : Horn.WordRAM.Input) : ℕ :=
  27*Nat.log2 (Horn.WordRAM.size input+2)+2

theorem clear_agrees {start cap : ℕ} {memory expected : ℕ → ℤ}
    (table : ∀ a, a<start → memory a=expected a)
    (zero : ∀ a, start≤a → expected a=0) :
    ∀ a, a<cap → Allocation.clear memory start (cap-start) a=expected a := by
  intro a below
  by_cases earlier : a<start
  · rw [Allocation.clear_frame (by omega)]
    exact table a earlier
  · rw [Allocation.clear_zero (by omega),zero a (by omega)]

/-- The Horn subroutine starts from a literal copy of its ordinary cold input
below the reserved caller arena; no prepared state or answer is assumed. -/
theorem invokeHorn {w cap : ℕ} (input : Horn.WordRAM.Input) (data : Data 32)
    (width : hornWidth input≤w) (arena : 2^hornWidth input≤cap)
    (registers : data.1=fun _ => 0)
    (memory : ∀ a, a<cap → data.2 a=(initial (r:=32) (Horn.WordRAM.encode input)).data.2 a) :
    ∃ result : Data 32, ∃ steps,
      Structured.Exec w Horn.WordRAM.program data result steps ∧
      steps+1≤120*(Horn.WordRAM.size input+1) ∧
      Fits w (result.1 Horn.WordRAM.Reg.output) ∧
      (result.1 Horn.WordRAM.Reg.output=0 ∨ result.1 Horn.WordRAM.Reg.output=1) ∧
      (result.1 Horn.WordRAM.Reg.output=1 ↔ Horn.Satisfiable input.2.rules.toList) ∧
      (∀ a, 2^hornWidth input≤a → result.2 a=data.2 a) := by
  obtain ⟨_,result,steps,execution,budget,fits,boolean,correct⟩ :=
    Horn.WordRAM.program_verified input (hornWidth input) (by rfl)
  have framed := execution.frame_mono width data.2
  have start : (initial (r:=32) (Horn.WordRAM.encode input)).data.frame
      (2^hornWidth input) data.2=data := by
    apply Prod.ext
    · exact registers.symm
    · funext a
      dsimp only [Data.frame]
      split_ifs with small
      · exact (memory a (by omega)).symm
      · rfl
  rw [start] at framed
  refine ⟨result.frame (2^hornWidth input) data.2,steps,framed,budget,
    WordBounds.fits_mono width fits,boolean,correct,?_⟩
  intro a outside
  simp [Data.frame,show ¬a<2^hornWidth input by omega]

/-- An initialized table is turned into the exact cold-input convention and
passed to Horn. Both the clearing loop and all thirty-two register resets are
included in the execution and its cost. -/
def coldInvokeHorn : Structured.Code 32 :=
  .seq coldGap (.seq reset32 Horn.WordRAM.program)

theorem coldInvokeHorn_exec {w start cap : ℕ} (input : Horn.WordRAM.Input) (data : Data 32)
    (index : data.1 1=start) (length : data.1 2=start) (arenaReg : data.1 5=cap)
    (within : start≤cap) (word : Fits w cap) (unit : Fits w 1)
    (width : hornWidth input≤w) (arena : 2^hornWidth input≤cap)
    (table : ∀ a, a<start → data.2 a=(initial (r:=32) (Horn.WordRAM.encode input)).data.2 a)
    (zero : ∀ a, start≤a → (initial (r:=32) (Horn.WordRAM.encode input)).data.2 a=0) :
    ∃ result : Data 32, ∃ steps,
      Structured.Exec w coldInvokeHorn data result steps ∧
      steps+1≤4*(cap-start)+38+120*(Horn.WordRAM.size input+1) ∧
      Fits w (result.1 Horn.WordRAM.Reg.output) ∧
      (result.1 Horn.WordRAM.Reg.output=0 ∨ result.1 Horn.WordRAM.Reg.output=1) ∧
      (result.1 Horn.WordRAM.Reg.output=1 ↔ Horn.Satisfiable input.2.rules.toList) ∧
      (∀ a, cap≤a → result.2 a=data.2 a) := by
  have gap := coldGap_exec data index length arenaReg within word unit
  let cleared : Data 32 :=
    (Allocation.registers data.1 cap start start cap,Allocation.clear data.2 start (cap-start))
  have zeroFits : Fits w 0 := by
    simpa using Allocation.nat_fits_le (a:=0) (b:=1) unit (by omega)
  have reset := reset32_exec cleared zeroFits
  obtain ⟨result,steps,run,budget,fits,boolean,correct,frame⟩ :=
    invokeHorn input (fun _ => 0,cleared.2) width arena rfl (clear_agrees table zero)
  have execution := gap.seq (reset.seq run)
  refine ⟨result,_,execution,?_,fits,boolean,correct,?_⟩
  · omega
  · intro a outside
    rw [frame a (by omega)]
    exact Allocation.clear_frame (by omega)

end LeanTrominoes.ImplicationGraph.TwoSATExpression

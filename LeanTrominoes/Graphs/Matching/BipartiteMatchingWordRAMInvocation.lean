/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMPolynomialTime
import LeanTrominoes.Computation.Compiler.FiniteTwoSATInvocation
import LeanTrominoes.Computation.Compiler.FiniteTwoSATRegisters

/-! # Calling matching on endpoint arrays constructed by another program

The caller clears unused low memory and resets all sixty-four registers before
running the original verified matching program. Clearing, resets, matching and
the eventual halt are all included in the instruction bound.
-/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
open ImplicationGraph.TwoSATExpression

/-- Width used by the matching operational certificate. -/
def callWidth (input : Input) : ℕ := 8*Nat.log2 (size input+2)+2

/-- Cold-input replay at any larger caller width. -/
theorem invoke_exec {w cap : ℕ} (input : Input) (data : ComplexityAbstract.RAM.Data 64)
    (width : callWidth input ≤ w) (arena : 2^callWidth input ≤ cap)
    (registers : data.1=fun _ => 0)
    (memory : ∀ a, a < cap → data.2 a=(initial (r:=64) (encode input)).data.2 a) :
    ∃ result : ComplexityAbstract.RAM.Data 64, ∃ steps,
      Structured.Exec w program data result steps ∧
      steps+1 ≤ 1000*(size input+1)^4 ∧ Fits w (result.1 Reg.output) ∧
      (result.1 Reg.output=0 ∨ result.1 Reg.output=1) ∧
      (result.1 Reg.output=1 ↔ predicate input) ∧
      (∀ a, 2^callWidth input ≤ a → result.2 a=data.2 a) := by
  obtain ⟨_,result,steps,execution,budget,fits,boolean,correct⟩ :=
    program_verified_quartic input (callWidth input) (by rfl)
  have framed := execution.frame_mono width data.2
  have start : (initial (r:=64) (encode input)).data.frame
      (2^callWidth input) data.2=data := by
    apply Prod.ext
    · exact registers.symm
    · funext a
      dsimp only [ComplexityAbstract.RAM.Data.frame]
      split_ifs with small
      · exact (memory a (by omega)).symm
      · rfl
  rw [start] at framed
  refine ⟨result.frame (2^callWidth input) data.2,steps,framed,budget,
    WordBounds.fits_mono width fits,boolean,correct,?_⟩
  intro a outside
  simp [ComplexityAbstract.RAM.Data.frame,show ¬a < 2^callWidth input by omega]

def reset64 : Structured.Code 64 := resetUpto 63 63 (by omega)

theorem reset64_exec {w : ℕ} (data : ComplexityAbstract.RAM.Data 64) (zero : Fits w 0) :
    Structured.Exec w reset64 data (fun _ => 0,data.2) 64 := by
  have registers : resetRegisters data.1 63=(fun _ => 0) := by
    funext i
    simp only [resetRegisters]
    exact ite_eq_left (by omega)
  simpa only [reset64,registers] using resetUpto_exec data 63 (by omega) zero

/-- The clearing loop retains the already constructed low endpoint records. -/
def coldInvoke : Structured.Code 64 :=
  .seq (coldGap.widen (by decide : 32 ≤ 64)) (.seq reset64 program)

theorem coldInvoke_exec {w start cap : ℕ} (input : Input) (data : ComplexityAbstract.RAM.Data 64)
    (index : data.1 1=start) (length : data.1 2=start) (arenaReg : data.1 5=cap)
    (within : start ≤ cap) (word : Fits w cap) (unit : Fits w 1)
    (width : callWidth input ≤ w) (arena : 2^callWidth input ≤ cap)
    (table : ∀ a, a < start → data.2 a=(initial (r:=64) (encode input)).data.2 a)
    (zero : ∀ a, start ≤ a → (initial (r:=64) (encode input)).data.2 a=0) :
    ∃ result : ComplexityAbstract.RAM.Data 64, ∃ steps,
      Structured.Exec w coldInvoke data result steps ∧
      steps+1 ≤ 4*(cap-start)+70+1000*(size input+1)^4 ∧
      Fits w (result.1 Reg.output) ∧
      (result.1 Reg.output=0 ∨ result.1 Reg.output=1) ∧
      (result.1 Reg.output=1 ↔ predicate input) ∧
      (∀ a, cap ≤ a → result.2 a=data.2 a) := by
  let low := data.restrict (by decide : 32 ≤ 64)
  have gap := coldGap_exec low index length arenaReg within word unit
  obtain ⟨cleared,clearRun,clearMemory,_,_⟩ := gap.widen_restrict (by decide : 32 ≤ 64)
  have zeroFits : Fits w 0 := by
    simpa using Allocation.nat_fits_le (a:=0) (b:=1) unit (by omega)
  have reset := reset64_exec cleared zeroFits
  have agreement : ∀ a, a < cap → cleared.2 a=(initial (r:=64) (encode input)).data.2 a := by
    rw [clearMemory]
    exact clear_agrees table zero
  obtain ⟨result,steps,run,budget,fits,boolean,correct,frame⟩ :=
    invoke_exec input (fun _ => 0,cleared.2) width arena rfl agreement
  have execution := clearRun.seq (reset.seq run)
  refine ⟨result,_,execution,?_,fits,boolean,correct,?_⟩
  · omega
  · intro a outside
    rw [frame a (by omega),clearMemory]
    exact Allocation.clear_frame (by omega)

/-- A simple polynomial arena contains every address visible at the certified
matching width. It can be computed by eight ordinary multiplications. -/
theorem callWidth_arena (input : Input) : 2^callWidth input ≤ 4*(size input+2)^8 := by
  have power : 2^Nat.log2 (size input+2) ≤ size input+2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (by omega : size input+2 ≠ 0)
  calc
    2^callWidth input = 4*(2^Nat.log2 (size input+2))^8 := by
      rw [callWidth,pow_add,Nat.mul_comm 8 _,pow_mul]
      norm_num
      omega
    _ ≤ 4*(size input+2)^8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left power 8)

end LeanTrominoes.BipartiteMatching.DenseWordRAM

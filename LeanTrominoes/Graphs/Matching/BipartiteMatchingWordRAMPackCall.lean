/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPackMemory
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMInvocation

/-! # Running matching on packed generated endpoint records -/
namespace LeanTrominoes.BipartiteMatching.PackWordRAM
open ComplexityAbstract.RAM

abbrev output : Fin 128 := Fin.castLE (by decide : 64 ≤ 128) DenseWordRAM.Reg.output

def call : Structured.Code 128 := DenseWordRAM.coldInvoke.widen (by decide : 64 ≤ 128)

theorem call_exec {w source cap : ℕ} (input : DenseWordRAM.Input) (original : ℕ → ℤ)
    (data : Data 128) (square : input.2.1=input.1)
    (left : ∀ i, (hi : i < input.2.2.length) → original (source+i)=(input.2.2[i]).1.val)
    (right : ∀ i, (hi : i < input.2.2.length) → original (source+input.2.2.length+i)=(input.2.2[i]).2.val)
    (memory : data.2=headerMemory (arraysMemory original source input.2.2.length) input.1 input.2.2.length)
    (index : data.1 1=4+2*input.2.2.length) (length : data.1 2=4+2*input.2.2.length)
    (arenaReg : data.1 5=cap) (within : 4+2*input.2.2.length ≤ cap)
    (word : Fits w cap) (unit : Fits w 1)
    (width : DenseWordRAM.callWidth input ≤ w) (arena : 2^DenseWordRAM.callWidth input ≤ cap) :
    ∃ result : Data 128, ∃ steps,
      Structured.Exec w call data result steps ∧
      steps+1 ≤ 4*(cap-(4+2*input.2.2.length))+70+1000*(DenseWordRAM.size input+1)^4 ∧
      Fits w (result.1 output) ∧ (result.1 output=0 ∨ result.1 output=1) ∧
      (result.1 output=1 ↔ DenseWordRAM.predicate input) := by
  let low := data.restrict (by decide : 64 ≤ 128)
  obtain ⟨answer,steps,run,budget,fits,boolean,correct,_⟩ :=
    DenseWordRAM.coldInvoke_exec input low index length arenaReg within word unit width arena
      (by simpa only [low,Data.restrict,memory] using packed_agrees input original source square left right)
      (initial_zero_after input)
  obtain ⟨result,largeRun,_,registers,_⟩ := run.widen_restrict (by decide : 64 ≤ 128)
  exact ⟨result,steps,largeRun,budget,by simpa only [registers] using fits,
    by simpa only [registers] using boolean,by simpa only [registers] using correct⟩

end LeanTrominoes.BipartiteMatching.PackWordRAM

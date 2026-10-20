/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPackHeader
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPackCall

/-! # Packing and deciding generated endpoint arrays on the bounded-word RAM -/
namespace LeanTrominoes.BipartiteMatching.PackWordRAM
open ComplexityAbstract.RAM

def program (d : ℕ) : Structured.Code 128 :=
  .seq copies (.seq (metadataCode d) (.seq footerCode call))

theorem program_exec {n d w source : ℕ} (input : DenseWordRAM.Input) (data : Data 128)
    (square : input.2.1=input.1) (side : input.1=vertexCount n d)
    (nValue : data.1 66=n) (leftBase : data.1 70=source)
    (rightBase : data.1 71=source+input.2.2.length) (edges : data.1 83=input.2.2.length)
    (lower : 4 ≤ source) (tablesFits : Fits w (source+2*input.2.2.length : ℕ))
    (capFits : Fits w (coldCapacity input.1 input.2.2.length)) (phaseFits : Fits w (2^d : ℕ))
    (left : ∀ i, (hi : i < input.2.2.length) → data.2 (source+i)=(input.2.2[i]).1.val)
    (right : ∀ i, (hi : i < input.2.2.length) → data.2 (source+input.2.2.length+i)=(input.2.2[i]).2.val)
    (leftFits : ∀ i, i < input.2.2.length → Fits w (data.2 (source+i)))
    (rightFits : ∀ i, i < input.2.2.length → Fits w (data.2 (source+input.2.2.length+i)))
    (width : DenseWordRAM.callWidth input ≤ w) :
    ∃ result : Data 128, ∃ steps,
      Structured.Exec w (program d) data result steps ∧
      steps+1 ≤ 18*input.2.2.length+75+
        (4*(coldCapacity input.1 input.2.2.length-(4+2*input.2.2.length))+70+
          1000*(DenseWordRAM.size input+1)^4) ∧
      Fits w (result.1 output) ∧ (result.1 output=0 ∨ result.1 output=1) ∧
      (result.1 output=1 ↔ DenseWordRAM.predicate input) := by
  obtain ⟨copied,copyRun,copyMemory,copyParams⟩ := copies_exec data leftBase rightBase edges lower tablesFits leftFits rightFits
  obtain ⟨counted,metadataRun,metadataMemory,nReg,capReg,metadataParams⟩ := metadata_exec (d:=d) copied
    (by simpa only [copyParams 66 (by decide) (by decide)] using nValue)
    (by simpa only [copyParams 83 (by decide) (by decide)] using edges)
    (by simpa only [side] using capFits) phaseFits
  have edgesReg : counted.1 83=input.2.2.length := by
    rw [metadataParams 83 (by decide) (by decide) (by decide),copyParams 83 (by decide) (by decide)]
    exact edges
  obtain ⟨headed,headerRun,headerMemory,index,length,arenaReg,_⟩ := footer_exec counted
    (nReg.trans (congrArg (fun x : ℕ => (x : ℤ)) side.symm)) edgesReg
    (by simpa only [side] using capReg) capFits
  have memory : headed.2=PackWordRAM.headerMemory (arraysMemory data.2 source input.2.2.length) input.1 input.2.2.length := by
    rw [headerMemory,metadataMemory,copyMemory]
    rfl
  have room : 4+2*input.2.2.length ≤ coldCapacity input.1 input.2.2.length := by
    have base : 1 ≤ 2*input.1+input.2.2.length+3 := by omega
    have grow : 2*input.1+input.2.2.length+3 ≤ (2*input.1+input.2.2.length+3)^8 :=
      by simpa only [pow_one] using pow_le_pow_right₀ base (show 1 ≤ 8 by omega)
    unfold coldCapacity
    omega
  have arena : 2^DenseWordRAM.callWidth input ≤ coldCapacity input.1 input.2.2.length := by
    have h := DenseWordRAM.callWidth_arena input
    simpa only [DenseWordRAM.size,square,coldCapacity,two_mul,Nat.add_assoc] using h
  obtain ⟨result,steps,callRun,budget,fits,boolean,correct⟩ := call_exec input data.2 headed square left right memory
    index length arenaReg room capFits (Allocation.nat_fits_le (a:=1) capFits (by omega)) width arena
  refine ⟨result,_,copyRun.seq (metadataRun.seq (headerRun.seq callRun)),?_,fits,boolean,correct⟩
  omega

end LeanTrominoes.BipartiteMatching.PackWordRAM

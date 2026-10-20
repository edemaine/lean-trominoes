/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMFreshControls

/-! # Full fresh-workspace coordinate testing in the original RAM -/
namespace LeanTrominoes.Domino.WordRAM.Binary.FreshProbe
open ComplexityAbstract.RAM
variable {n d : ℕ}

structure GlobalEnvironment (p : Layout) (memory : ℕ → ℕ) (b : ℤ) : Prop where
  determinant_bits : ∀ i< p.length, memory (p.global 1+i)≤1
  twice_bits : ∀ i< p.length, memory (p.global 2+i)≤1
  zero : ∀ i< p.length, memory (p.global 0+i)=0
  determinant_value : value memory (p.global 1) p.length=b.natAbs
  twice_value : value memory (p.global 2) p.length=2*b.natAbs
  nonzero : b≠0
  guard : 4*b.natAbs≤2^p.length

structure Resources (data : Data) (p : Layout) (w : ℕ) : Prop where
  factor : Fits w (p.circuitSlots+3 : ℕ)
  request : Fits w ((p.circuitSlots+3)*data.1 Reserve.precision : ℕ)
  endpoint : Fits w (data.1 Reserve.frontier+(p.circuitSlots+3)*data.1 Reserve.precision : ℕ)
  unit : Fits w (1:ℕ)
  values : ∀ pair∈ProbeHeaders.moves, Fits w ((reserved data p.circuitSlots).1 pair.2)
  four : Fits w (4:ℕ)
  indices : ∀ slot∈[p.outputSlot,p.circuitSlots,p.circuitSlots+1,p.circuitSlots+2], Fits w slot
  products : ∀ slot∈[p.outputSlot,p.circuitSlots,p.circuitSlots+1,p.circuitSlots+2],
    Fits w (slot*(reserved data p.circuitSlots).1 Reserve.precision : ℕ)
  addresses : ∀ slot∈[p.outputSlot,p.circuitSlots,p.circuitSlots+1,p.circuitSlots+2],
    Fits w ((reserved data p.circuitSlots).1 Reserve.base+slot*(reserved data p.circuitSlots).1 Reserve.precision : ℕ)

noncomputable def callProgram (d : ℕ) (direction coordinate : Fin d) : Code :=
  let e := Circuit.rawNumeratorCircuit d direction coordinate
  .seq (prepareProgram (e.compile (d*d+2*d)).output (d*d+2*d+(e.compile (d*d+2*d)).nodes.length))
    ((rawProbeProgram d direction coordinate).embed 64)

theorem prepared_environment (data : Data) (p : Layout) (b : ℤ)
    (base : p.base=data.1 Reserve.frontier) (length : p.length=data.1 Reserve.precision)
    (h : GlobalEnvironment p data.2 b) : Probe.Environment p.geometry (prepared data p.outputSlot p.circuitSlots).2 b := by
  have same (global : Fin 3) (i : ℕ) (hi : i< p.length) :
      (prepared data p.outputSlot p.circuitSlots).2 (p.global global+i)=data.2 (p.global global+i) := by
    apply prepared_before
    have before := p.global_before global
    rw [←base]
    omega
  constructor
  · intro i hi; rw [geometry_determinant,same 1 i hi]; exact h.determinant_bits i hi
  · intro i hi; rw [geometry_twice,same 2 i hi]; exact h.twice_bits i hi
  · intro i hi; rw [geometry_zero,same 0 i hi]; exact h.zero i hi
  · intro i hi
    rw [geometry_remainder]
    exact prepared_digit data p base length (p.circuitSlots+1) i (by omega) hi
  · rw [geometry_determinant,geometry_precision,value_congr (same 1)]; exact h.determinant_value
  · rw [geometry_twice,geometry_precision,value_congr (same 2)]; exact h.twice_value
  · exact h.nonzero
  · exact h.guard

theorem extended_caller (before : Data) (result : NaturalData 64) (i : Fin 128) (high : 64≤ i.val) :
    (result.extend (NaturalData.upper (r:=64) (s:=64) before)).1 i=before.1 i := by
  let j : Fin 64 := ⟨i.val-64,by have := i.isLt; omega⟩
  have same : j.natAdd 64=i := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    dsimp only [j]
    omega
  rw [←same,NaturalData.extend_right]
  rfl

theorem call_exec {w : ℕ} (B : BasisData n d) (u v : Fin n) (direction coordinate : Fin d)
    (data : Data) (p : Layout)
    (base : p.base=data.1 Reserve.frontier) (length : p.length=data.1 Reserve.precision)
    (inputLength : p.length=WordRAM.precision B)
    (output : p.outputSlot=((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).output)
    (slots : p.circuitSlots=d*d+2*d+((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length)
    (zero : p.global 0=data.1 ProbeHeaders.zero) (determinant : p.global 1=data.1 ProbeHeaders.determinant)
    (twice : p.global 2=data.1 ProbeHeaders.twice)
    (first : data.1 ProbeHeaders.firstOrigin=(sourceLayout B u v p.base).source 1)
    (second : data.1 ProbeHeaders.secondOrigin=(sourceLayout B u v p.base).source 2)
    (environment : GlobalEnvironment p data.2 B.basis.det)
    (original : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< p.length,
      data.2 ((sourceLayout B u v p.base).source block+slot*p.length+i)=
        inputMemory B ((sourceLayout B u v p.base).source block+slot*p.length+i))
    (sourceBefore : ∀ block : Fin 3, ∀ slot< SourceLoad.count d block, ∀ i< p.length,
      (sourceLayout B u v p.base).source block+slot*p.length+i< p.base)
    (sourceFits : ∀ block : Fin 3, Fits w (BatchCopy.bound ((sourceLayout B u v p.base).source block) p.base p.length 0
      (SourceLoad.start d block) (SourceLoad.count d block)))
    (resources : Resources data p w)
    (circuitFits : Fits w (Circuit.resourceBound p.base p.length p.circuitSlots)) :
    ∃ result cost, NaturalData.Exec w (callProgram d direction coordinate) data result cost ∧
      cost≤4*((p.circuitSlots+3)*p.length)+
        (26*p.length^2+26*p.length+16)*((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length+
        29*p.length^2+65*p.length+107+(7*p.length+11)*(d*d+2*d) ∧
      (0< result.1 (Numerator.G.valid.castAdd 64) ↔ B.basis.det∣
        (Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)) ∧
      result.1 (Numerator.G.parity.castAdd 64)≤1 ∧
      (B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v) →
        ((Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)/B.basis.det)%2=
          (result.1 (Numerator.G.parity.castAdd 64) : ℤ)) ∧
      result.1 Reserve.frontier=data.1 Reserve.frontier+(p.circuitSlots+3)*p.length ∧
      result.1 Reserve.base=data.1 Reserve.frontier ∧
      (∀ i : Fin 128, 64≤ i.val → i≠Reserve.frontier → i≠Reserve.base → result.1 i=data.1 i) ∧
      (∀ address, (address< p.base ∨ p.base+(p.circuitSlots+3)*p.length≤ address) → result.2 address=data.2 address) := by
  let before := prepared data p.outputSlot p.circuitSlots
  have prep := prepare_exec data p.outputSlot p.circuitSlots resources.factor resources.request resources.endpoint resources.unit
    resources.values resources.four resources.indices resources.products resources.addresses
  have numControls := prepared_numerator_controls data p base length zero determinant twice
  have srcControls : SourceLoad.Controls (sourceLayout B u v p.base)
      (NaturalData.lower (r:=64) (s:=64) before) := by
    rw [base]
    apply prepared_source_controls
    · rw [←length]; exact inputLength
    · simpa only [base] using first
    · simpa only [base] using second
  have small : Fits w (3:ℕ) := Allocation.nat_fits_le resources.four (by omega)
  have widths : Numerator.Widths p.geometry w := widths p small (by rw [base,length]; exact resources.endpoint)
  obtain ⟨result,probeCost,run,bound,valid,bit,parity,controls,frame⟩ := raw_probe_exec B u v direction coordinate
    (NaturalData.lower (r:=64) (s:=64) before) p.geometry inputLength srcControls
    (by
      rw [←inputLength]
      intro block slot hs i hi
      change before.2 _=inputMemory B _
      rw [prepared_before data p.outputSlot p.circuitSlots _ (by rw [←base]; exact sourceBefore block slot hs i hi)]
      exact original block slot hs i hi)
    (by rw [←inputLength]; intro block slot hs i hi; exact Or.inl (sourceBefore block slot hs i hi))
    (by simpa only [←inputLength] using sourceFits) numControls widths
    (prepared_environment data p B.basis.det base length environment)
    (by rw [geometry_numerator,geometry_precision,output])
    (by intro slot hn ha hd j hj; simpa only [←slots,Circuit.slotBase,geometry_precision] using geometry_outside p slot hn ha hd j hj)
    (by intro slot hs he i hi; exact prepared_digit data p base length slot i (by rw [slots]; omega) hi)
    (by simpa only [geometry_precision,←slots] using circuitFits)
  have call := NaturalData.call_exec (r:=64) (s:=64) run
  have full := prep.seq call
  refine ⟨result.extend (NaturalData.upper (r:=64) (s:=64) before),(4*((p.circuitSlots+3)*data.1 Reserve.precision)+34)+probeCost,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [callProgram,output,slots] using full
  · rw [←length]
    change probeCost≤(26*p.length^2+26*p.length+16)*
      ((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length+
      29*p.length^2+65*p.length+73+(7*p.length+11)*(d*d+2*d) at bound
    omega
  · simpa only [NaturalData.extend_left] using valid
  · simpa only [NaturalData.extend_left] using bit
  · simpa only [NaturalData.extend_left] using parity
  · rw [extended_caller before result _ (by decide)]
    change (prepared data p.outputSlot p.circuitSlots).1 Reserve.frontier=_
    rw [prepared,ProbeHeaders.state_high _ _ _ _ (by decide),reserved_frontier,←length]
  · rw [extended_caller before result _ (by decide)]
    change (prepared data p.outputSlot p.circuitSlots).1 Reserve.base=_
    rw [prepared,ProbeHeaders.state_high _ _ _ _ (by decide),reserved_base]
  · intro i high notFront notBase
    rw [extended_caller before result i high]
    exact prepared_caller data p.outputSlot p.circuitSlots i high notFront notBase
  · intro address outsideFresh
    have outsideCircuit : address< p.base ∨ Circuit.slotBase p.base p.geometry.precision
        (d*d+2*d+((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).nodes.length)≤ address := by
      rw [←slots]
      rcases outsideFresh with before | after
      · exact Or.inl before
      · right; change p.base+p.circuitSlots*p.length≤ address; nlinarith
    have outsideA : address< p.geometry.absolute ∨ p.geometry.absolute+p.geometry.precision≤ address := by
      rw [geometry_absolute,geometry_precision]
      rcases outsideFresh with before | after
      · left; nlinarith
      · right; nlinarith
    have outsideR : address< p.geometry.remainder ∨ p.geometry.remainder+p.geometry.precision≤ address := by
      rw [geometry_remainder,geometry_precision]
      rcases outsideFresh with before | after
      · left; nlinarith
      · right; nlinarith
    have outsideD : address< p.geometry.difference ∨ p.geometry.difference+p.geometry.precision≤ address := by
      rw [geometry_difference,geometry_precision]
      rcases outsideFresh with before | after
      · left; nlinarith
      · right; nlinarith
    change result.2 address=data.2 address
    rw [frame address outsideCircuit outsideA outsideR outsideD]
    change (prepared data p.outputSlot p.circuitSlots).2 address=data.2 address
    rw [prepared_memory,Reserve.clear_apply,←base,←length,if_neg (by omega)]

end LeanTrominoes.Domino.WordRAM.Binary.FreshProbe

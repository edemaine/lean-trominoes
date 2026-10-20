/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCollect

/-! # One polynomial scalar bound covers every fresh probe instruction -/
namespace LeanTrominoes.Domino.WordRAM.Binary.FreshProbe
open ComplexityAbstract.RAM

def scalarBound (slots highWater : ℕ) : ℕ := 20*(slots+5)*(highWater+1)

def headerRegisters : List (Fin 128) := [Reserve.precision,Reserve.frontier,ProbeHeaders.zero,ProbeHeaders.determinant,
  ProbeHeaders.twice,ProbeHeaders.firstOrigin,ProbeHeaders.secondOrigin]

theorem resources_of_bound {w : ℕ} (data : Data) (p : Layout) (slots highWater : ℕ)
    (capacity : p.circuitSlots≤ slots) (small : 4≤ highWater)
    (headers : ∀ i∈headerRegisters, data.1 i≤ highWater)
    (width : Fits w (scalarBound slots highWater)) : Resources data p w := by
  have fits (n : ℕ) (bound : n≤ scalarBound slots highWater) : Fits w n := Allocation.nat_fits_le width bound
  have headerFits (i : Fin 128) (member : i∈headerRegisters) : Fits w (data.1 i) := by
    apply fits
    have bound := headers i member
    unfold scalarBound
    nlinarith only [bound]
  have length : data.1 Reserve.precision≤ highWater := headers _ (by simp [headerRegisters])
  have front : data.1 Reserve.frontier≤ highWater := headers _ (by simp [headerRegisters])
  have pLength : (reserved data p.circuitSlots).1 Reserve.precision=data.1 Reserve.precision :=
    reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide)
  have pBase : (reserved data p.circuitSlots).1 Reserve.base=data.1 Reserve.frontier := reserved_base data p.circuitSlots
  have slotBound (slot : ℕ) (within : slot∈[p.outputSlot,p.circuitSlots,p.circuitSlots+1,p.circuitSlots+2]) : slot≤ slots+2 := by
    have before := p.output_before
    simp only [List.mem_cons,List.not_mem_nil,or_false] at within
    rcases within with rfl | rfl | rfl | rfl <;> omega
  have productBound : (p.circuitSlots+3)*data.1 Reserve.precision≤(slots+3)*highWater :=
    Nat.mul_le_mul (by omega) length
  constructor
  · apply fits
    unfold scalarBound
    nlinarith
  · apply fits
    unfold scalarBound
    nlinarith only [productBound]
  · apply fits
    unfold scalarBound
    nlinarith only [productBound,front]
  · exact fits 1 (by unfold scalarBound; nlinarith)
  · intro pair hp
    simp only [ProbeHeaders.moves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | rw [pLength]
        apply fits
        unfold scalarBound
        nlinarith only [length]
      | rw [pBase]
        apply fits
        unfold scalarBound
        nlinarith only [front]
      | rw [reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide)]
        exact headerFits _ (by simp [headerRegisters])
  · exact fits 4 (by unfold scalarBound; nlinarith)
  · intro slot within
    have bound := slotBound slot within
    apply fits
    unfold scalarBound
    nlinarith only [bound]
  · intro slot within
    rw [pLength]
    have product := Nat.mul_le_mul (slotBound slot within) length
    apply fits
    unfold scalarBound
    nlinarith only [product]
  · intro slot within
    rw [pLength,pBase]
    have product := Nat.mul_le_mul (slotBound slot within) length
    apply fits
    unfold scalarBound
    nlinarith only [product,front]

theorem circuit_fits_of_bound {w : ℕ} (p : Layout) (slots highWater : ℕ)
    (capacity : p.circuitSlots≤ slots) (base : p.base≤ highWater) (length : p.length≤ highWater)
    (width : Fits w (scalarBound slots highWater)) : Fits w (Circuit.resourceBound p.base p.length p.circuitSlots) := by
  apply Allocation.nat_fits_le width
  have product := Nat.mul_le_mul (Nat.add_le_add_right capacity 1) (Nat.add_le_add_right length 1)
  unfold Circuit.resourceBound scalarBound
  nlinarith only [product,base]

theorem source_fits_of_bound {n d w : ℕ} (B : BasisData n d) (u v : Fin n) (base length slots highWater : ℕ)
    (arity : d*d+2*d≤ slots) (source : ∀ block, (sourceLayout B u v base).source block≤ highWater)
    (baseBound : base≤ highWater) (lengthBound : length≤ highWater)
    (width : Fits w (scalarBound slots highWater)) (block : Fin 3) :
    Fits w (BatchCopy.bound ((sourceLayout B u v base).source block) base length 0
      (SourceLoad.start d block) (SourceLoad.count d block)) := by
  have countBound : SourceLoad.count d block≤ slots := by
    fin_cases block <;> norm_num [SourceLoad.count] <;> omega
  have endBound : SourceLoad.start d block+SourceLoad.count d block≤ slots := by
    fin_cases block <;> norm_num [SourceLoad.start,SourceLoad.count,Circuit.slotBase] <;> omega
  have first := Nat.mul_le_mul (Nat.add_le_add_right countBound 1) (Nat.add_le_add_right lengthBound 1)
  have second := Nat.mul_le_mul (Nat.add_le_add_right endBound 1) (Nat.add_le_add_right lengthBound 1)
  have sourceBound := source block
  apply Allocation.nat_fits_le width
  unfold BatchCopy.bound scalarBound
  simp only [Nat.zero_add]
  nlinarith only [first,second,sourceBound,baseBound,lengthBound]

end LeanTrominoes.Domino.WordRAM.Binary.FreshProbe

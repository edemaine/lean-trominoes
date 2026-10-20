/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMFreshPrepare

/-! # Fresh allocation establishes the two decoder call conventions -/
namespace LeanTrominoes.Domino.WordRAM.Binary.FreshProbe
open ComplexityAbstract.RAM

theorem prepared_numerator_controls (data : Data) (p : Layout)
    (base : p.base=data.1 Reserve.frontier) (length : p.length=data.1 Reserve.precision)
    (zero : p.global 0=data.1 ProbeHeaders.zero)
    (determinant : p.global 1=data.1 ProbeHeaders.determinant)
    (twice : p.global 2=data.1 ProbeHeaders.twice) :
    Numerator.Controls p.geometry (NaturalData.lower (r:=64) (s:=64) (prepared data p.outputSlot p.circuitSlots)) := by
  apply ProbeHeaders.numerator_controls
  · rw [geometry_precision,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide)]
    exact length
  · rw [geometry_numerator,reserved_base,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide),base,length]
  · rw [geometry_zero,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide)]
    exact zero
  · rw [geometry_determinant,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide)]
    exact determinant
  · rw [geometry_twice,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide)]
    exact twice
  · rw [geometry_absolute,reserved_base,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide),base,length]
  · rw [geometry_remainder,reserved_base,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide),base,length]
  · rw [geometry_difference,reserved_base,reserved_reg data p.circuitSlots _ (by decide) (by decide) (by decide),base,length]

theorem prepared_source_controls {n d : ℕ} (B : BasisData n d) (u v : Fin n) (data : Data) (output slots : ℕ)
    (length : data.1 Reserve.precision=WordRAM.precision B)
    (first : data.1 ProbeHeaders.firstOrigin=(sourceLayout B u v (data.1 Reserve.frontier)).source 1)
    (second : data.1 ProbeHeaders.secondOrigin=(sourceLayout B u v (data.1 Reserve.frontier)).source 2) :
    SourceLoad.Controls (sourceLayout B u v (data.1 Reserve.frontier))
      (NaturalData.lower (r:=64) (s:=64) (prepared data output slots)) := by
  apply ProbeHeaders.source_controls
  · rw [reserved_reg data slots _ (by decide) (by decide) (by decide)]
    exact length
  · exact reserved_base data slots
  · rw [reserved_reg data slots _ (by decide) (by decide) (by decide)]
    exact first
  · rw [reserved_reg data slots _ (by decide) (by decide) (by decide)]
    exact second

theorem prepared_digit (data : Data) (p : Layout)
    (base : p.base=data.1 Reserve.frontier) (length : p.length=data.1 Reserve.precision)
    (slot i : ℕ) (within : slot< p.circuitSlots+3) (digit : i< p.length) :
    (prepared data p.outputSlot p.circuitSlots).2 (p.base+slot*p.length+i)=0 := by
  rw [prepared_memory,←base,←length]
  exact cleared_digit p data.2 slot i within digit

theorem prepared_before (data : Data) (output slots address : ℕ) (before : address< data.1 Reserve.frontier) :
    (prepared data output slots).2 address=data.2 address := by
  rw [prepared_memory,Reserve.clear_apply,if_neg (by omega)]

end LeanTrominoes.Domino.WordRAM.Binary.FreshProbe

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderState

/-! # Reading the next high-to-low numerator digit -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM
attribute [local simp] R.numerator R.denominator R.remainder R.difference R.precision
  R.count R.position R.address R.bit R.zero R.one NaturalData.set

def read1 (data : WideData) := data.set R.position (data.1 R.position-data.1 R.one)
def read2 (data : WideData) := (read1 data).set R.address ((read1 data).1 R.numerator+(read1 data).1 R.position)
def readState (data : WideData) := (read2 data).set R.bit ((read2 data).2 ((read2 data).1 R.address))
attribute [local simp] read1 read2 readState

theorem readBit_exec {w : ℕ} (data : WideData) (one : data.1 R.one=1)
    (positive : 0< data.1 R.position)
    (positionFits : Fits w (data.1 R.position-1 : ℕ))
    (addressFits : Fits w (data.1 R.numerator+(data.1 R.position-1) : ℕ))
    (bitFits : Fits w (data.2 (data.1 R.numerator+(data.1 R.position-1)))) :
    NaturalData.Exec w readBit data (readState data) 3 := by
  have h1 : NaturalData.Exec w (.atom (.arithmetic .sub R.position R.position R.one)) data (read1 data) 1 := by
    apply NaturalData.sub_exec
    · omega
    · simpa [one] using positionFits
  have h2 : NaturalData.Exec w (.atom (.arithmetic .add R.address R.numerator R.position)) (read1 data) (read2 data) 1 := by
    apply NaturalData.add_exec
    simpa [one] using addressFits
  have h3 : NaturalData.Exec w (.atom (.load R.bit R.address)) (read2 data) (readState data) 1 := by
    apply NaturalData.load_exec
    · simpa [one] using addressFits
    · simpa [one] using bitFits
  exact h1.seq (h2.seq h3)

theorem readState_controls {g : Geometry} {position : ℕ} {data : WideData}
    (h : Controls g (position+1) data) : Controls g position (readState data) := by
  constructor <;> simp_all only [readState,read2,read1,NaturalData.set]
  all_goals simp [h.numerator,h.denominator,h.remainder,h.difference,h.precision,h.count,h.position,h.zero,h.one]

theorem MemoryRepresents.of_memory {g : Geometry} {source : ℕ → ℕ} {position : ℕ} {before after : WideData}
    (h : MemoryRepresents g source position before) (same : after.2=before.2) :
    MemoryRepresents g source position after := by
  constructor
  · simpa only [same] using h.numerator
  · simpa only [same] using h.denominator
  · simpa only [same] using h.remainder_bits
  · simpa only [same] using h.result
  · simpa only [same] using h.frame

theorem readState_bit {g : Geometry} {source : ℕ → ℕ} {position : ℕ} {data : WideData}
    (within : position< g.count) (h : Controls g (position+1) data)
    (memory : MemoryRepresents g source (position+1) data) :
    (readState data).1 R.bit=source (g.numerator+position) := by
  simp [h.one,h.position,h.numerator,memory.numerator position within]

end LeanTrominoes.Domino.WordRAM.Binary.Remainder

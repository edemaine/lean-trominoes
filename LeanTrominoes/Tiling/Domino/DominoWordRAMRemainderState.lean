/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderCalls

/-! # Memory and arithmetic invariant for binary long remainder -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM

/-- Four disjoint arrays: numerator, denominator, remainder, difference. -/
structure Geometry where
  base : Fin 4 → ℕ
  precision : ℕ
  count : ℕ
  disjoint : ∀ i j : Fin 4, i≠j → ∀ a< (if i=0 then count else precision),
    ∀ b< (if j=0 then count else precision), base i+a≠base j+b

namespace Geometry
abbrev numerator (g : Geometry) := g.base 0
abbrev denominator (g : Geometry) := g.base 1
abbrev remainder (g : Geometry) := g.base 2
abbrev difference (g : Geometry) := g.base 3
def length (g : Geometry) (i : Fin 4) := if i=0 then g.count else g.precision

theorem outside (g : Geometry) (i j : Fin 4) (different : i≠j) (a : ℕ) (within : a< g.length i) :
    g.base i+a< g.base j ∨ g.base j+g.length j≤ g.base i+a := by
  by_contra h
  push Not at h
  have off : g.base i+a-g.base j< g.length j := by omega
  have diseq := g.disjoint i j different a within (g.base i+a-g.base j) off
  omega

def borrowLayout (g : Geometry) : Binary.Layout where
  first := g.remainder
  second := g.denominator
  output := g.difference
  length := g.precision
  first_disjoint := by
    intro i hi j hj _
    exact g.disjoint 3 2 (by decide) i hi j hj
  second_disjoint := by
    intro i hi j hj _
    exact g.disjoint 3 1 (by decide) i hi j hj

def copyLayout (g : Geometry) : ComplementLayout where
  input := g.difference
  output := g.remainder
  length := g.precision
  disjoint := by
    intro i hi j hj _
    exact g.disjoint 2 3 (by decide) i hi j hj
end Geometry

structure Input (g : Geometry) (source : ℕ → ℕ) : Prop where
  numerator_bits : ∀ i< g.count, source (g.numerator+i)≤1
  denominator_bits : ∀ i< g.precision, source (g.denominator+i)≤1
  denominator_positive : 0< value source g.denominator g.precision
  denominator_small : 2*value source g.denominator g.precision≤2^g.precision

structure Controls (g : Geometry) (position : ℕ) (data : WideData) : Prop where
  numerator : data.1 R.numerator=g.numerator
  denominator : data.1 R.denominator=g.denominator
  remainder : data.1 R.remainder=g.remainder
  difference : data.1 R.difference=g.difference
  precision : data.1 R.precision=g.precision
  count : data.1 R.count=g.count
  position : data.1 R.position=position
  zero : data.1 R.zero=0
  one : data.1 R.one=1

structure MemoryRepresents (g : Geometry) (source : ℕ → ℕ) (position : ℕ) (data : WideData) : Prop where
  numerator : ∀ j< g.count, data.2 (g.numerator+j)=source (g.numerator+j)
  denominator : ∀ j< g.precision, data.2 (g.denominator+j)=source (g.denominator+j)
  remainder_bits : ∀ j< g.precision, data.2 (g.remainder+j)≤1
  result : value data.2 g.remainder g.precision=
    value source (g.numerator+position) (g.count-position)%value source g.denominator g.precision
  frame : ∀ address,
    (address< g.remainder ∨ g.remainder+g.precision≤ address) →
    (address< g.difference ∨ g.difference+g.precision≤ address) → data.2 address=source address

/-- Private registers survive every arithmetic call exactly. -/
theorem extend_high (data : WideData) (result : Data) (i : Fin 32) (high : 16≤ i.val) :
    (extend result (upper data)).1 i=data.1 i := by
  let j : Fin 16 := ⟨i.val-16,by have := i.isLt; omega⟩
  have same : j.natAdd 16=i := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    dsimp only [j]
    omega
  rw [← same,extend_right]
  rfl

theorem Controls.extend {g : Geometry} {position : ℕ} {data : WideData}
    (h : Controls g position data) (result : Data) :
    Controls g position (Binary.extend result (upper data)) := by
  constructor
  · rw [extend_high data result _ (by decide)]; exact h.numerator
  · rw [extend_high data result _ (by decide)]; exact h.denominator
  · rw [extend_high data result _ (by decide)]; exact h.remainder
  · rw [extend_high data result _ (by decide)]; exact h.difference
  · rw [extend_high data result _ (by decide)]; exact h.precision
  · rw [extend_high data result _ (by decide)]; exact h.count
  · rw [extend_high data result _ (by decide)]; exact h.position
  · rw [extend_high data result _ (by decide)]; exact h.zero
  · rw [extend_high data result _ (by decide)]; exact h.one

/-- Original operands and all memory outside the two scratch blocks. -/
structure Sources (g : Geometry) (source : ℕ → ℕ) (data : WideData) : Prop where
  numerator : ∀ j< g.count, data.2 (g.numerator+j)=source (g.numerator+j)
  denominator : ∀ j< g.precision, data.2 (g.denominator+j)=source (g.denominator+j)
  frame : ∀ address,
    (address< g.remainder ∨ g.remainder+g.precision≤address) →
    (address< g.difference ∨ g.difference+g.precision≤address) → data.2 address=source address

def MemoryRepresents.sources {g source position data} (h : MemoryRepresents g source position data) :
    Sources g source data := ⟨h.numerator,h.denominator,h.frame⟩

theorem Sources.remainder_write {g : Geometry} {source : ℕ → ℕ} {before after : WideData}
    (h : Sources g source before)
    (frame : ∀ address, (address< g.remainder ∨ g.remainder+g.precision≤address) →
      after.2 address=before.2 address) : Sources g source after := by
  constructor
  · intro j hj
    rw [frame _ (g.outside 0 2 (by decide) j hj)]
    exact h.numerator j hj
  · intro j hj
    rw [frame _ (g.outside 1 2 (by decide) j hj)]
    exact h.denominator j hj
  · intro address outsideR outsideD
    rw [frame address outsideR]
    exact h.frame address outsideR outsideD

theorem Sources.difference_write {g : Geometry} {source : ℕ → ℕ} {before after : WideData}
    (h : Sources g source before)
    (frame : ∀ address, (address< g.difference ∨ g.difference+g.precision≤address) →
      after.2 address=before.2 address) : Sources g source after := by
  constructor
  · intro j hj
    rw [frame _ (g.outside 0 3 (by decide) j hj)]
    exact h.numerator j hj
  · intro j hj
    rw [frame _ (g.outside 1 3 (by decide) j hj)]
    exact h.denominator j hj
  · intro address outsideR outsideD
    rw [frame address outsideD]
    exact h.frame address outsideR outsideD

theorem Geometry.value_preserved (g : Geometry) (i j : Fin 4) (different : i≠j)
    (before after : ℕ → ℕ)
    (frame : ∀ address, (address< g.base j ∨ g.base j+g.length j≤address) →
      after address=before address) :
    value after (g.base i) (g.length i)=value before (g.base i) (g.length i) := by
  apply value_congr
  intro k hk
  exact frame _ (g.outside i j different k hk)

end LeanTrominoes.Domino.WordRAM.Binary.Remainder

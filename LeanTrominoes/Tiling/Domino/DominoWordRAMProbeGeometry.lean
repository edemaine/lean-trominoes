/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMProbeHeaders

/-! # A fresh circuit and three working arrays above the global determinant -/
namespace LeanTrominoes.Domino.WordRAM.Binary.FreshProbe

structure Layout where
  base : ℕ
  length : ℕ
  outputSlot : ℕ
  circuitSlots : ℕ
  output_before : outputSlot< circuitSlots
  global : Fin 3 → ℕ
  global_disjoint : ∀ i j : Fin 3, i≠j → global i+length≤ global j ∨ global j+length≤ global i
  global_before : ∀ i, global i+length≤ base

def Layout.freshSlot (p : Layout) : Fin 4 → ℕ | 0 => p.outputSlot | 1 => p.circuitSlots | 2 => p.circuitSlots+1 | _ => p.circuitSlots+2

def index : Fin 7 → Fin 3 ⊕ Fin 4 | 0 => .inr 0 | 1 => .inl 0 | 2 => .inl 1 | 3 => .inl 2 | 4 => .inr 1 | 5 => .inr 2 | _ => .inr 3

def Layout.address (p : Layout) : Fin 3 ⊕ Fin 4 → ℕ
  | .inl i => p.global i
  | .inr i => p.base+p.freshSlot i*p.length

theorem index_injective : Function.Injective index := by decide

theorem Layout.freshSlot_injective (p : Layout) : Function.Injective p.freshSlot := by
  intro i j equal
  have before := p.output_before
  fin_cases i <;> fin_cases j <;> simp_all [Layout.freshSlot] <;> omega

def Layout.geometry (p : Layout) : Numerator.Geometry where
  base := fun i => p.address (index i)
  precision := p.length
  disjoint := by
    intro i j different a ha b hb equal
    have different' : index i≠index j := fun same => different (index_injective same)
    generalize ei : index i=x at different' equal
    generalize ej : index j=y at different' equal
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have apart := p.global_disjoint x y (by simpa using different')
        change p.global x+a=p.global y+b at equal
        rcases apart with left | right <;> omega
      | inr y =>
        have before := p.global_before x
        change p.global x+a=p.base+p.freshSlot y*p.length+b at equal
        omega
    | inr x =>
      cases y with
      | inl y =>
        have before := p.global_before y
        change p.base+p.freshSlot x*p.length+a=p.global y+b at equal
        omega
      | inr y =>
        have ne : p.freshSlot x≠p.freshSlot y := fun same => different' (by rw [p.freshSlot_injective same])
        exact Circuit.slot_disjoint ne ha hb equal

@[simp] theorem geometry_precision (p : Layout) : p.geometry.precision=p.length := rfl
@[simp] theorem geometry_numerator (p : Layout) : p.geometry.numerator=p.base+p.outputSlot*p.length := rfl
@[simp] theorem geometry_zero (p : Layout) : p.geometry.zero=p.global 0 := rfl
@[simp] theorem geometry_determinant (p : Layout) : p.geometry.determinant=p.global 1 := rfl
@[simp] theorem geometry_twice (p : Layout) : p.geometry.twice=p.global 2 := rfl
@[simp] theorem geometry_absolute (p : Layout) : p.geometry.absolute=p.base+p.circuitSlots*p.length := rfl
@[simp] theorem geometry_remainder (p : Layout) : p.geometry.remainder=p.base+(p.circuitSlots+1)*p.length := rfl
@[simp] theorem geometry_difference (p : Layout) : p.geometry.difference=p.base+(p.circuitSlots+2)*p.length := rfl

theorem geometry_outside (p : Layout) (i : Fin 7) (notN : i≠0) (notA : i≠4) (notD : i≠6)
    (j : ℕ) (within : j< p.length) :
    p.geometry.base i+j< p.base ∨ p.base+p.circuitSlots*p.length≤ p.geometry.base i+j := by
  fin_cases i
  · exact (notN rfl).elim
  · left; have before := p.global_before 0; change p.global 0+j< p.base; omega
  · left; have before := p.global_before 1; change p.global 1+j< p.base; omega
  · left; have before := p.global_before 2; change p.global 2+j< p.base; omega
  · exact (notA rfl).elim
  · right; change p.base+p.circuitSlots*p.length≤ p.base+(p.circuitSlots+1)*p.length+j; nlinarith
  · exact (notD rfl).elim

theorem cleared_digit (p : Layout) (memory : ℕ → ℕ) (slot i : ℕ) (within : slot< p.circuitSlots+3) (digit : i< p.length) :
    ComplexityAbstract.RAM.NaturalData.clear memory p.base ((p.circuitSlots+3)*p.length) (p.base+slot*p.length+i)=0 := by
  rw [Reserve.clear_apply,if_pos]
  constructor
  · omega
  · have mul := Nat.mul_le_mul_right p.length (Nat.succ_le_of_lt within)
    nlinarith

theorem Layout.endpoint_bound (p : Layout) (i : Fin 7) :
    p.geometry.base i+p.length≤p.base+(p.circuitSlots+3)*p.length := by
  fin_cases i
  · change p.base+p.outputSlot*p.length+p.length≤_
    have h := Nat.mul_le_mul_right p.length (Nat.succ_le_of_lt p.output_before)
    nlinarith only [h]
  · have h := p.global_before 0
    change p.global 0+p.length≤_
    nlinarith only [h]
  · have h := p.global_before 1
    change p.global 1+p.length≤_
    nlinarith only [h]
  · have h := p.global_before 2
    change p.global 2+p.length≤_
    nlinarith only [h]
  · change p.base+p.circuitSlots*p.length+p.length≤_
    nlinarith
  · change p.base+(p.circuitSlots+1)*p.length+p.length≤_
    nlinarith
  · change p.base+(p.circuitSlots+2)*p.length+p.length≤_
    nlinarith

theorem widths {w : ℕ} (p : Layout) (small : ComplexityAbstract.RAM.Fits w (3:ℕ))
    (endpoint : ComplexityAbstract.RAM.Fits w (p.base+(p.circuitSlots+3)*p.length : ℕ)) :
    Numerator.Widths p.geometry w := by
  constructor
  · exact small
  · exact ComplexityAbstract.RAM.Allocation.nat_fits_le endpoint (by change p.length≤p.base+(p.circuitSlots+3)*p.length; nlinarith)
  · intro slot
    exact ComplexityAbstract.RAM.Allocation.nat_fits_le endpoint (p.endpoint_bound slot)

end LeanTrominoes.Domino.WordRAM.Binary.FreshProbe

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripRawValidity
import LeanTrominoes.CompletionStripReduction

/-! # Natural-arithmetic occupancy of a periodic prefill -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw

def Covered (t : Tromino) (input : PeriodicStripTrominoPrefill) (x y : Nat) : Prop :=
  ∃ p ∈ input.motif, ∃ k : Fin 3,
    (biasedCell t (bound input) p k).2 = bound input+y ∧
      (biasedCell t (bound input) p k).1 % input.period = (bound input+x) % input.period

theorem covers_point_iff (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p : Placement Unit) (hp : p ∈ input.motif) (k : Fin 3) (x y : Nat) :
    ((biasedCell t (bound input) p k).2 = bound input+y ∧
      (biasedCell t (bound input) p k).1 % input.period = (bound input+x) % input.period) ↔
    (point t p k).2 = (y : Int) ∧ (input.period : Int) ∣ (x : Int)-(point t p k).1 := by
  have h := biasedCell_eq t input p hp k
  change ((biasedCell t (bound input) p k).1 : Int) = (bound input : Int)+(point t p k).1 ∧
    ((biasedCell t (bound input) p k).2 : Int) = (bound input : Int)+(point t p k).2 at h
  rw [mod_eq_iff,h.1,Nat.cast_add]
  have diff : (bound input : Int)+(point t p k).1 - ((bound input : Int)+x) = (point t p k).1-x := by ring
  rw [diff]
  apply and_congr (by omega)
  constructor <;> intro divides
  · convert (Int.dvd_neg.mpr divides) using 1 <;> ring
  · convert (Int.dvd_neg.mpr divides) using 1 <;> ring

theorem covered_iff (t : Tromino) (input : PeriodicStripTrominoPrefill) (x y : Nat) (hy : y < input.height) :
    Covered t input x y ↔ ((x : Int),(y : Int)) ∈ (occupiedStrip t input).carrier := by
  rw [PeriodicStrip.mem_carrier_iff]
  constructor
  · rintro ⟨p,hp,k,hk⟩
    have h := (covers_point_iff t input p hp k x y).mp hk
    refine ⟨by omega,by change (y : Int) < (input.height : Int); exact_mod_cast hy,point t p k,?_,h⟩
    exact List.mem_flatMap.mpr ⟨p,hp,(PeriodicTrominoPrefill.mem_placementCells t p _).mpr
      ((mem_cells_iff_point t p _).mpr ⟨k,rfl⟩)⟩
  · rintro ⟨_,_,c,hc,ey,divides⟩
    obtain ⟨p,hp,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨k,rfl⟩ := (mem_cells_iff_point t p c).mp ((PeriodicTrominoPrefill.mem_placementCells t p c).mp hc)
    exact ⟨p,hp,k,(covers_point_iff t input p hp k x y).mpr ⟨ey,divides⟩⟩

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw

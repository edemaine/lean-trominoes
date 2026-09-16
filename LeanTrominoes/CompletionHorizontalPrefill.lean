/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripValidity
import LeanTrominoes.TrominoCompletionTranslation
import Mathlib.Tactic.Ring

/-! # Finite motifs for horizontally periodic prefills -/
namespace LeanTrominoes.CompletionPattern.HorizontalPrefill

def prescribed (t : Tromino) (period : Int) (motif : List (Placement Unit)) : Set (Finset Cell) :=
  {f | ∃ p ∈ motif, ∃ i : Int, f = (p.shift (i*period,0)).cells (fun _ => t.cells)}

theorem strip_prescribed (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    input.periodic.prescribed t = prescribed t input.period input.motif := by
  ext f
  rw [PeriodicStripTrominoPrefill.prescribed_iff]
  simp only [prescribed,Set.mem_setOf_eq,PeriodicStripTrominoPrefill.translate,Placement.shift_cells_image]

theorem prescribed_append (t : Tromino) (period : Int) (a b : List (Placement Unit)) :
    prescribed t period (a++b) = prescribed t period a ∪ prescribed t period b := by
  ext f
  simp only [prescribed,Set.mem_setOf_eq,List.mem_append,Set.mem_union]
  aesop

theorem shift_commute (p : Placement Unit) (a b : Cell) : (p.shift a).shift b = (p.shift b).shift a := by
  apply Placement.ext
  · rfl
  · rfl
  · apply Prod.ext <;> dsimp [Placement.shift,Cell.add] <;> omega

theorem prescribed_shift (t : Tromino) (period : Int) (motif : List (Placement Unit)) (v : Cell) :
    prescribed t period (motif.map fun p => p.shift v) =
      (fun f => f.image (Cell.add v)) '' prescribed t period motif := by
  ext f
  constructor
  · rintro ⟨_,hq,i,rfl⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    rw [shift_commute,Placement.shift_cells_image]
    exact ⟨_,⟨p,hp,i,rfl⟩,rfl⟩
  · rintro ⟨g,⟨p,hp,i,rfl⟩,rfl⟩
    refine ⟨p.shift v,List.mem_map.mpr ⟨p,hp,rfl⟩,i,?_⟩
    rw [shift_commute]
    simp only [Placement.shift_cells_image]

def expand (stride : Int) (count : Nat) (motif : List (Placement Unit)) : List (Placement Unit) :=
  (List.range count).flatMap fun i => motif.map fun p => p.shift ((i:Int)*stride,0)

theorem prescribed_expand (t : Tromino) (stride : Int) (count : Nat) (hc : 0 < count)
    (motif : List (Placement Unit)) :
    prescribed t (stride*count) (expand stride count motif) = prescribed t stride motif := by
  ext f
  constructor
  · rintro ⟨_,hq,i,rfl⟩
    obtain ⟨j,_,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    refine ⟨p,hp,(j:Int)+i*count,?_⟩
    congr 1
    apply Placement.ext
    · rfl
    · rfl
    · apply Prod.ext <;> dsimp [Placement.shift,Cell.add] <;> ring
  · rintro ⟨p,hp,i,rfl⟩
    have positive : (0:Int) < count := by exact_mod_cast hc
    have lower := Int.emod_nonneg i (ne_of_gt positive)
    have upper := Int.emod_lt_of_pos i positive
    let j : Nat := (i%count).toNat
    have hj : j < count := by dsimp [j]; omega
    have castj : (j : Int) = i%count := by dsimp [j]; omega
    have eq : (j : Int)+(i/count)*count = i := by
      rw [castj,Int.mul_comm (i/count)]
      exact Int.emod_add_mul_ediv i count
    refine ⟨p.shift ((j:Int)*stride,0),List.mem_flatMap.mpr
      ⟨j,List.mem_range.mpr hj,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,i/count,?_⟩
    congr 1
    apply Placement.ext
    · rfl
    · rfl
    · apply Prod.ext <;> dsimp [Placement.shift,Cell.add]
      · calc
          i*stride+p.offset.1 = ((j:Int)+(i/count)*count)*stride+p.offset.1 := by rw [eq]
          _ = _ := by ring
      · omega

end LeanTrominoes.CompletionPattern.HorizontalPrefill

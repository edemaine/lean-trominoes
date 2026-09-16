/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.StripFrontier

/-! # Explicit complements within a periodic strip -/
namespace LeanTrominoes.PeriodicStrip

/-- All cells in one rectangular period. -/
def fundamentalCells (s : PeriodicStrip) : List Cell :=
  (List.range s.period).flatMap fun (x : Nat) =>
    (List.range s.width).map fun (y : Nat) => ((x : Int),(y : Int))

theorem mem_fundamentalCells (s : PeriodicStrip) (c : Cell) :
    c ∈ s.fundamentalCells ↔ s.InFundamentalDomain c := by
  simp only [fundamentalCells,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    dsimp [InFundamentalDomain]
    omega
  · rintro ⟨hx,hp,hy,hw⟩
    exact ⟨c.1.toNat,by omega,c.2.toNat,by omega,by apply Prod.ext <;> dsimp <;> omega⟩

def complement (s : PeriodicStrip) : PeriodicStrip :=
  ⟨s.width,s.period,s.fundamentalCells.filter fun c => !s.contains c⟩

theorem mem_complement_motif (s : PeriodicStrip) (c : Cell) :
    c ∈ s.complement.motif ↔ s.InFundamentalDomain c ∧ c ∉ s.carrier := by
  simp only [complement,List.mem_filter,mem_fundamentalCells]
  have h := s.contains_eq_true_iff c
  cases eq : s.contains c <;> simp_all

theorem complement_wellFormed (s : PeriodicStrip) (hw : 0 < s.width) (hp : 0 < s.period) :
    s.complement.IsWellFormed := by
  refine ⟨hw,hp,?_⟩
  intro c hc
  exact ((mem_complement_motif s c).mp hc).1

theorem complement_carrier (s : PeriodicStrip) (hp : 0 < s.period) :
    s.complement.carrier = {c | 0 ≤ c.2 ∧ c.2 < (s.width : Int)} \ s.carrier := by
  ext c
  rw [s.complement.mem_carrier_iff]
  constructor
  · rintro ⟨hy,hw,b,hb,ey,divides⟩
    obtain ⟨_,absent⟩ := (mem_complement_motif s b).mp hb
    refine ⟨⟨hy,hw⟩,?_⟩
    have same := s.mem_carrier_congr_x (row := c.2) divides
    apply (not_congr same).mp
    simpa only [← ey,Prod.mk.eta] using absent
  · rintro ⟨⟨hy,hw⟩,absent⟩
    let b : Cell := (c.1 % s.period,c.2)
    have positive : (0 : Int) < s.period := by exact_mod_cast hp
    have divides : (s.period : Int) ∣ c.1 - b.1 := by
      dsimp [b]
      refine ⟨c.1 / s.period,?_⟩
      have := Int.emod_add_mul_ediv c.1 s.period
      omega
    refine ⟨hy,hw,b,?_,rfl,divides⟩
    apply (mem_complement_motif s b).mpr
    refine ⟨⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ positive,hy,hw⟩,?_⟩
    exact (not_congr (s.mem_carrier_congr_x divides)).mpr absent

theorem fundamentalCells_length (s : PeriodicStrip) : s.fundamentalCells.length = s.period * s.width := by
  simp [fundamentalCells,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

theorem complement_motif_length (s : PeriodicStrip) : s.complement.motif.length ≤ s.period * s.width := by
  exact (List.length_filter_le _ _).trans_eq (fundamentalCells_length s)

end LeanTrominoes.PeriodicStrip

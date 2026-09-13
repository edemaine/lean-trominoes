/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementEnvelope

/-! # Enlarging the background period without changing its periodic holes -/

namespace LeanTrominoes.KeyedPeriodicComplement

def repeatMask (copies n : Nat) (holes : Polyomino) : Polyomino :=
  (square (copies*n)).filter (fun c => residue n c ∈ holes)

theorem repeatMask_carrier {copies n : Nat} (copies_pos : 0 < copies) (hn : 0 < n)
    (holes : Polyomino) : holesRegion (copies*n) (repeatMask copies n holes) = holesRegion n holes := by
  have pos : 0 < copies*n := Nat.mul_pos copies_pos hn
  have divisor : (n : Int) ∣ (copies*n : Nat) := by
    exact ⟨copies,by simp [Nat.cast_mul,Int.mul_comm]⟩
  ext c
  simp only [holesRegion,Set.mem_setOf_eq,repeatMask,Finset.mem_filter,
    residue_mem_square pos,and_true,true_and]
  simp only [residue,Int.emod_emod_of_dvd _ divisor]

private theorem corner_residue {copies n : Nat} (hn : 96 ≤ n) (x : Int)
    (bounds : 0 ≤ x ∧ x < (copies*n : Nat))
    (corner : x < 18 ∨ (copies*n : Nat)-18 ≤ x) :
    x % (n : Int) < 18 ∨ (n : Int)-18 ≤ x % (n : Int) := by
  rcases corner with left | right
  · have eq : x % (n : Int) = x := Int.emod_eq_of_lt bounds.1 (by omega)
    exact Or.inl (by simpa only [eq] using left)
  · have lo : 0 ≤ x - (copies : Int)*n+n := by
      simp only [Nat.cast_mul] at bounds right
      omega
    have hi : x - (copies : Int)*n+n < n := by
      simp only [Nat.cast_mul] at bounds
      omega
    have eq : x % (n : Int) = x - (copies : Int)*n+n := by
      calc
        x % (n : Int) = (x - (copies : Int)*n+n) % n := by simp [Int.add_emod,Int.sub_emod,Int.mul_emod]
        _ = x - (copies : Int)*n+n := Int.emod_eq_of_lt lo hi
    right
    rw [eq]
    simp only [Nat.cast_mul] at right
    omega

theorem repeatMask_admissible {copies n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) :
    AdmissibleHoles (copies*n) (repeatMask copies n holes) := by
  intro c hc
  obtain ⟨squareMem,hole⟩ := Finset.mem_filter.mp hc
  have bounds := (mem_square _ c).mp squareMem
  have source := admissible (residue n c) hole
  refine ⟨?_,?_⟩
  · simpa only [residue,Int.emod_emod_of_dvd _ (Int.dvd_of_emod_eq_zero period)] using source.1
  · intro corner
    exact source.2 ⟨corner_residue hn c.1 ⟨bounds.1,bounds.2.1⟩ corner.1,
      corner_residue hn c.2 ⟨bounds.2.2.1,bounds.2.2.2⟩ corner.2⟩

end LeanTrominoes.KeyedPeriodicComplement

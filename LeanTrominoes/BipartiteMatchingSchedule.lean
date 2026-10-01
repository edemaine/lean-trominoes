/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingPhaseBound

/-! # Square-root bound for the solver's successful-phase trace -/
namespace LeanTrominoes.BipartiteMatching

def Schedule (vertices : Nat) : Nat → Nat → List (Nat × Nat) → Prop
  | _,_,[] => True
  | free,lower,(count,depth)::rest =>
    0 < count ∧ count ≤ free ∧ lower < depth ∧ count*depth ≤ vertices ∧
      Schedule vertices (count-1) depth rest

theorem Schedule.weaken {vertices free lower : Nat} {trace : List (Nat × Nat)}
    (valid : Schedule vertices free lower trace) (more : Nat) (bound : free ≤ more) :
    Schedule vertices more lower trace := by
  cases trace with
  | nil => trivial
  | cons entry rest =>
    obtain ⟨count,depth⟩ := entry
    exact ⟨valid.1,valid.2.1.trans bound,valid.2.2⟩

theorem Schedule.potential {vertices free lower : Nat} {trace : List (Nat × Nat)}
    (valid : Schedule vertices free lower trace) :
    trace.length ≤ (Nat.sqrt vertices+1-lower)+min free (Nat.sqrt vertices+1) := by
  induction trace generalizing free lower with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨count,depth⟩ := entry
    obtain ⟨positive,bound,increase,density,later⟩ := valid
    have tail := ih later
    have sq := Nat.lt_succ_sqrt vertices
    by_cases short : depth < Nat.sqrt vertices+1
    · simp only [List.length_cons]
      omega
    · have small : count < Nat.sqrt vertices+1 := by
        have product : count*(Nat.sqrt vertices+1) ≤ vertices :=
          (Nat.mul_le_mul_left count (by omega)).trans density
        nlinarith
      simp only [List.length_cons]
      omega

theorem Schedule.length_bound {vertices free lower : Nat} {trace : List (Nat × Nat)}
    (valid : Schedule vertices free lower trace) : trace.length ≤ 2*(Nat.sqrt vertices+1) := by
  have bound := valid.potential
  omega

end LeanTrominoes.BipartiteMatching

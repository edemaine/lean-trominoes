/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTwoSATCore

/-! # Anchoring each binary clause at its first literal

The paper's locality concerns differences of offsets. A common offset can be
arbitrarily large. Because every translate of each clause is imposed, moving
that clause's anchor preserves exactly the same assignments.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph
variable {V : Type*} {d : Nat}

def normalizeClause : Clause V d → Clause V d
  | none => none
  | some (a,b) => some ((a.1,0),(b.1,b.2-a.2))
def normalize (formula : Formula V d) : Formula V d := formula.map normalizeClause

def LocalDifferences (formula : Formula V d) : Prop :=
  ∀ a b, some (a,b) ∈ formula → ∀ i, (b.2 i-a.2 i).natAbs ≤ 1

theorem normalize_satisfies (formula : Formula V d) (model : V → Lattice d → Prop) :
    Satisfies (normalize formula) model ↔ Satisfies formula model := by
  constructor
  · intro normalized c member z
    have one := normalized (normalizeClause c) (List.mem_map.mpr ⟨c,member,rfl⟩)
    cases c with
    | none => exact one z
    | some pair =>
      obtain ⟨a,b⟩ := pair
      have clause := one (z+a.2)
      change Truth model a.1 (z+a.2+0) ∨ Truth model b.1 (z+a.2+(b.2-a.2)) at clause
      have equal : z+a.2+(b.2-a.2)=z+b.2 := by abel
      simpa [Holds,equal] using clause
  · intro original c member z
    obtain ⟨clause,originalMember,rfl⟩ := List.mem_map.mp member
    cases clause with
    | none => exact original none originalMember z
    | some pair =>
      obtain ⟨a,b⟩ := pair
      have clause := original (some (a,b)) originalMember (z-a.2)
      change Truth model a.1 (z-a.2+a.2) ∨ Truth model b.1 (z-a.2+b.2) at clause
      have equal : z-a.2+b.2=z+(b.2-a.2) := by abel
      simpa [Holds,normalizeClause,equal] using clause

theorem normalize_satisfiable (formula : Formula V d) : Satisfiable (normalize formula) ↔ Satisfiable formula :=
  exists_congr (fun model => normalize_satisfies formula model)

theorem normalize_local (formula : Formula V d) (locality : LocalDifferences formula) : Local (normalize formula) := by
  intro a b member
  obtain ⟨c,hc,equal⟩ := List.mem_map.mp member
  cases c with
  | none => simp [normalizeClause] at equal
  | some pair =>
    obtain ⟨x,y⟩ := pair
    have same : ((x.1,0),(y.1,y.2-x.2))=(a,b) := Option.some.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    refine ⟨by simp,?_⟩
    exact locality x y hc

@[simp] theorem normalize_length (formula : Formula V d) : (normalize formula).length=formula.length := by simp [normalize]

end LeanTrominoes.PeriodicTwoSAT

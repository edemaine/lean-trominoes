/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSeededCoRE

/-! # Effective finite witnesses for consequences of a fixed periodic formula

A clause forced by all global solutions is already forced by some finite
window. The window can be found by exhaustive finite Boolean search. This
lets a verified global decoder be used on a sufficiently large local patch.
-/
namespace LeanTrominoes.PeriodicCNF
namespace FiniteConsequences
variable {V : Type} [DecidableEq V]

abbrev Clause (V : Type) := List ((V × Cell) × Bool)

def Holds (clause : Clause V) (a : V → Cell → Bool) : Prop :=
  ∃ l ∈ clause, a l.1.1 l.1.2 = l.2

def falsifyingSeed (clause : Clause V) : Seed V :=
  clause.map fun l => (l.1,!l.2)

omit [DecidableEq V] in
theorem not_holds_iff (clause : Clause V) (a : V → Cell → Bool) :
    ¬ Holds clause a ↔ ∀ pin ∈ falsifyingSeed clause, a pin.1.1 pin.1.2 = pin.2 := by
  simp only [Holds,not_exists,not_and,falsifyingSeed,List.forall_mem_map]
  apply forall_congr'
  intro l
  apply imp_congr_right
  intro _
  cases l.2 <;> cases a l.1.1 l.1.2 <;> simp

def Entails (f : PeriodicCNF V) (clause : Clause V) : Prop :=
  ∀ a, f.Satisfies a → Holds clause a

def FiniteEntails (f : PeriodicCNF V) (clause : Clause V) (radius : Nat) : Prop :=
  ¬ FiniteSearch.Check (FiniteSearch.withSeed f (falsifyingSeed clause) radius)

instance (f : PeriodicCNF V) (clause : Clause V) (radius : Nat) :
    Decidable (FiniteEntails f clause radius) := by
  unfold FiniteEntails
  infer_instance

theorem entails_iff (f : PeriodicCNF V) (clause : Clause V) :
    Entails f clause ↔ ∃ radius, FiniteEntails f clause radius := by
  have global : Entails f clause ↔ ¬ f.Seeded (falsifyingSeed clause) := by
    simp only [Entails,Seeded,not_exists,not_and,← not_holds_iff,not_not]
  rw [global,FiniteSearch.seeded_iff,not_forall]
  rfl

theorem finiteEntails_sound {f : PeriodicCNF V} {clause : Clause V} {radius : Nat}
    (forced : FiniteEntails f clause radius) (a : V → Cell → Bool)
    (patch : ∀ c ∈ TrominoAssignment.boxCellList radius,
      ∀ sourceClause ∈ f.clauses, sourceClause.Holds a c) : Holds clause a := by
  by_contra failure
  apply forced
  apply (FiniteSearch.check_iff _).2
  refine ⟨fun p => a p.1 p.2,(FiniteSearch.holds_withSeed _ _ _ _).2 ⟨?_,?_⟩⟩
  · exact (FiniteSearch.holds_instantiate _ _ _).2 patch
  · exact (not_holds_iff _ _).1 failure

noncomputable def radius (f : PeriodicCNF V) (clause : Clause V)
    (forced : Entails f clause) : Nat := Nat.find ((entails_iff f clause).1 forced)

theorem radius_spec (f : PeriodicCNF V) (clause : Clause V) (forced : Entails f clause) :
    FiniteEntails f clause (radius f clause forced) :=
  Nat.find_spec ((entails_iff f clause).1 forced)

end FiniteConsequences
end LeanTrominoes.PeriodicCNF

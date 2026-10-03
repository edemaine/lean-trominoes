/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNF

/-! # Ordinary finite CNF formulas and their zero-offset periodic embedding -/
namespace LeanTrominoes.FiniteCNF

abbrev Literal (V : Type*) := V × Bool
abbrev Clause (V : Type*) := List (Literal V)
abbrev Formula (V : Type*) := List (Clause V)

def Clause.Holds {V : Type*} (assignment : V → Bool) (clause : Clause V) : Prop :=
  ∃ literal∈clause, assignment literal.1=literal.2

def Satisfies {V : Type*} (formula : Formula V) (assignment : V → Bool) : Prop :=
  ∀ clause∈formula, Clause.Holds assignment clause

def Satisfiable {V : Type*} (formula : Formula V) : Prop := ∃ assignment, Satisfies formula assignment

def check {V : Type*} (formula : Formula V) (assignment : V → Bool) : Bool :=
  formula.all fun clause => clause.any fun literal => assignment literal.1==literal.2

theorem check_correct {V : Type*} (formula : Formula V) (assignment : V → Bool) :
    check formula assignment=true ↔ Satisfies formula assignment := by
  simp [check,Satisfies,Clause.Holds]

def rename {V W : Type*} (f : V → W) (formula : Formula V) : Formula W :=
  formula.map fun clause => clause.map fun literal => (f literal.1,literal.2)

theorem satisfies_rename {V W : Type*} (f : V → W) (formula : Formula V) (assignment : W → Bool) :
    Satisfies (rename f formula) assignment ↔ Satisfies formula (assignment ∘ f) := by
  simp [rename,Satisfies,Clause.Holds,Function.comp_def]

theorem satisfies_append {V : Type*} (a b : Formula V) (assignment : V → Bool) :
    Satisfies (a++b) assignment ↔ Satisfies a assignment ∧ Satisfies b assignment := by
  simp [Satisfies,List.mem_append,or_imp,forall_and]

/-- Every translate is an independent copy of the same finite SAT instance. -/
def periodize {V : Type*} (formula : Formula V) : PeriodicCNF V :=
  ⟨formula.map fun clause => clause.map fun literal => ⟨literal.1,(0,0),literal.2⟩⟩

theorem satisfies_periodize {V : Type*} (formula : Formula V) (assignment : V → Cell → Bool) :
    (periodize formula).Satisfies assignment ↔
      ∀ c : Cell, Satisfies formula (fun v => assignment v c) := by
  constructor
  · intro h c clause hc
    obtain ⟨literal,hl,truth⟩ := h c _ (List.mem_map.mpr ⟨clause,hc,rfl⟩)
    obtain ⟨l,member,rfl⟩ := List.mem_map.mp hl
    exact ⟨l,member,by simpa [PeriodicLiteral.Holds,Cell.add] using truth⟩
  · intro h c clause hc
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp hc
    obtain ⟨l,hl,truth⟩ := h c original member
    exact ⟨⟨l.1,(0,0),l.2⟩,List.mem_map.mpr ⟨l,hl,rfl⟩,
      by simpa [PeriodicLiteral.Holds,Cell.add] using truth⟩

theorem satisfiable_periodize {V : Type*} (formula : Formula V) :
    (periodize formula).Satisfiable ↔ Satisfiable formula := by
  constructor
  · rintro ⟨assignment,h⟩
    exact ⟨fun v => assignment v (0,0),(satisfies_periodize formula assignment).mp h (0,0)⟩
  · rintro ⟨assignment,h⟩
    exact ⟨fun v _ => assignment v,(satisfies_periodize formula _).mpr (fun _ => h)⟩

end LeanTrominoes.FiniteCNF

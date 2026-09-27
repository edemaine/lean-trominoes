/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicHornCNF

/-! # Dual Horn formulas by complementing every literal -/
namespace LeanTrominoes.PeriodicCNF
variable {V : Type*}

def complementLiterals (f : PeriodicCNF V) : PeriodicCNF V :=
  ⟨f.clauses.map (fun c => c.map (fun l => { l with value := !l.value }))⟩

/-- At most one distinct negative literal in each clause. -/
def IsDualHorn (f : PeriodicCNF V) : Prop := f.complementLiterals.IsHorn

private theorem complement_bool (a b : Bool) : a=(!b) ↔ (!a)=b := by cases a <;> cases b <;> decide

theorem complement_satisfies (f : PeriodicCNF V) (model : V → Cell → Bool) :
    f.complementLiterals.Satisfies model ↔ f.Satisfies (fun a z => !(model a z)) := by
  simp [complementLiterals,Satisfies,PeriodicClause.Holds,
    PeriodicLiteral.Holds,complement_bool,-Bool.not_eq_eq_eq_not]

theorem complement_satisfiable (f : PeriodicCNF V) : f.complementLiterals.Satisfiable ↔ f.Satisfiable := by
  constructor
  · rintro ⟨model,h⟩
    exact ⟨_,(complement_satisfies f model).mp h⟩
  · rintro ⟨model,h⟩
    refine ⟨fun a z => !(model a z),(complement_satisfies f _).mpr ?_⟩
    simpa using h

theorem dualHorn_period_one (f : PeriodicCNF V) (horn : f.IsDualHorn) (sat : f.Satisfiable) :
    ∃ model : V → Bool, f.Satisfies (fun a _ => model a) := by
  obtain ⟨model,h⟩ := horn_period_one f.complementLiterals horn ((complement_satisfiable f).mpr sat)
  exact ⟨fun a => !(model a),(complement_satisfies f _).mp h⟩

theorem dualHorn_satisfiable_iff_finite (f : PeriodicCNF V) (horn : f.IsDualHorn) :
    f.Satisfiable ↔ Horn.Satisfiable (f.complementLiterals.hornRules.map Horn.PeriodicRule.erase) :=
  (complement_satisfiable f).symm.trans (horn_satisfiable_iff_finite f.complementLiterals horn)

end LeanTrominoes.PeriodicCNF

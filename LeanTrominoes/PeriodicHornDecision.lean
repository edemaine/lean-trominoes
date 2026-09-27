/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDualHorn
import LeanTrominoes.PeriodicHornSolver

/-! # Total decisions and explicit period-one models for periodic Horn CNF

The checks reject formulas outside the requested Horn class. Repeated literal
occurrences are allowed. No locality or coordinate bound is required.
-/
namespace LeanTrominoes
namespace PeriodicClause
variable {V : Type*} [DecidableEq V]
instance decidableIsHorn (c : PeriodicClause V) : Decidable c.IsHorn := by
  unfold IsHorn
  infer_instance
end PeriodicClause
namespace PeriodicCNF
variable {V : Type*} [DecidableEq V]
instance decidableIsHorn (f : PeriodicCNF V) : Decidable f.IsHorn := by
  unfold IsHorn
  infer_instance
instance decidableIsDualHorn (f : PeriodicCNF V) : Decidable f.IsDualHorn := by
  unfold IsDualHorn
  infer_instance

def hornCheck (f : PeriodicCNF V) : Bool := decide f.IsHorn && Horn.periodicCheck f.hornRules

def dualHornCheck (f : PeriodicCNF V) : Bool := hornCheck f.complementLiterals

theorem hornCheck_correct (f : PeriodicCNF V) : hornCheck f=true ↔ f.IsHorn ∧ f.Satisfiable := by
  simp only [hornCheck,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨horn,checked⟩
    exact ⟨horn,(horn_satisfiable_iff_finite f horn).mpr ((Horn.check_correct _).mp checked)⟩
  · rintro ⟨horn,sat⟩
    exact ⟨horn,(Horn.check_correct _).mpr ((horn_satisfiable_iff_finite f horn).mp sat)⟩

theorem dualHornCheck_correct (f : PeriodicCNF V) : dualHornCheck f=true ↔ f.IsDualHorn ∧ f.Satisfiable := by
  rw [dualHornCheck,hornCheck_correct,complement_satisfiable]
  rfl

def hornModel (f : PeriodicCNF V) : V → Bool := Horn.periodicModel f.hornRules

def dualHornModel (f : PeriodicCNF V) (a : V) : Bool := !(hornModel f.complementLiterals a)

theorem hornModel_correct (f : PeriodicCNF V) (checked : hornCheck f=true) :
    f.Satisfies (fun a _ => hornModel f a) := by
  have raw := checked
  simp only [hornCheck,Bool.and_eq_true,decide_eq_true_eq] at raw
  exact (hornRules_correct f raw.1 _).mpr (Horn.periodicModel_correct f.hornRules raw.2)

theorem dualHornModel_correct (f : PeriodicCNF V) (checked : dualHornCheck f=true) :
    f.Satisfies (fun a _ => dualHornModel f a) :=
  (complement_satisfies f _).mp (hornModel_correct f.complementLiterals checked)

end PeriodicCNF
end LeanTrominoes

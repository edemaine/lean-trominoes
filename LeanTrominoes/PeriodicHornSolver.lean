/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornSolver

/-! # Executable Horn and dual Horn solvers in arbitrary dimensions -/
namespace LeanTrominoes.Horn
variable {V G : Type*} [AddGroup G]

/-- A dual Horn rule is a Horn rule applied to the complemented assignment. -/
def PeriodicDualSatisfies (rules : List (PeriodicRule V G)) (model : V → G → Prop) : Prop :=
  PeriodicSatisfies rules (fun a z => ¬model a z)

def PeriodicDualSatisfiable (rules : List (PeriodicRule V G)) : Prop :=
  ∃ model, PeriodicDualSatisfies rules model

theorem dual_satisfiable_iff (rules : List (PeriodicRule V G)) :
    PeriodicDualSatisfiable rules ↔ PeriodicSatisfiable rules := by
  classical
  constructor
  · rintro ⟨model,h⟩
    exact ⟨_,h⟩
  · rintro ⟨model,h⟩
    refine ⟨fun a z => ¬model a z,?_⟩
    simpa only [PeriodicDualSatisfies,not_not] using h

theorem dual_exists_period_one (rules : List (PeriodicRule V G)) (h : PeriodicDualSatisfiable rules) :
    ∃ model : V → Prop, PeriodicDualSatisfies rules (fun a _ => model a) := by
  classical
  obtain ⟨model,hm⟩ := exists_period_one rules ((dual_satisfiable_iff rules).mp h)
  refine ⟨fun a => ¬model a,?_⟩
  simpa only [PeriodicDualSatisfies,not_not] using hm

variable [DecidableEq V]

def periodicCheck (rules : List (PeriodicRule V G)) : Bool := check (rules.map PeriodicRule.erase)

theorem periodicCheck_correct (rules : List (PeriodicRule V G)) :
    periodicCheck rules=true ↔ PeriodicSatisfiable rules :=
  (check_correct _).trans (periodic_satisfiable_iff rules).symm

theorem periodicDualCheck_correct (rules : List (PeriodicRule V G)) :
    periodicCheck rules=true ↔ PeriodicDualSatisfiable rules :=
  (periodicCheck_correct rules).trans (dual_satisfiable_iff rules).symm

/-- The solver produces a period-one assignment by ignoring all offsets. -/
def periodicModel (rules : List (PeriodicRule V G)) (a : V) : Bool :=
  decide (a ∈ closure (rules.map PeriodicRule.erase))

theorem periodicModel_correct (rules : List (PeriodicRule V G)) (h : periodicCheck rules=true) :
    PeriodicSatisfies rules (fun a _ => periodicModel rules a=true) := by
  have finite := (check_iff_model (rules.map PeriodicRule.erase)).mp h
  have periodic := (constant_satisfies_iff rules _).mpr finite
  simpa only [periodicModel,decide_eq_true_eq] using periodic

theorem periodicDualModel_correct (rules : List (PeriodicRule V G)) (h : periodicCheck rules=true) :
    PeriodicDualSatisfies rules (fun a _ => (!periodicModel rules a)=true) := by
  have hm := periodicModel_correct rules h
  simpa only [PeriodicDualSatisfies,Bool.not_eq_true',Bool.not_eq_false] using hm

end LeanTrominoes.Horn

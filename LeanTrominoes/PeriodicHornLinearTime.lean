/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornIndexedTime
import LeanTrominoes.PeriodicHornSolver

/-! # Linear indexed-RAM decisions for periodic Horn and dual Horn SAT

Offsets are ignored when compiling to the finite quotient. Each reference
record is visited once; no arithmetic or search on its offset is needed.
The index domain `Fin n` is explicit, and all `n` variable slots are counted.
-/
namespace LeanTrominoes.Horn.PeriodicIndexed
variable {n : Nat} {G : Type*}

def quotient (rules : Array (PeriodicRule (Fin n) G)) : Indexed.Input n :=
  ⟨rules.map PeriodicRule.erase⟩

def check (rules : Array (PeriodicRule (Fin n) G)) : Bool := Indexed.check (quotient rules)

def model (rules : Array (PeriodicRule (Fin n) G)) : Fin n → Bool := Indexed.model (quotient rules)

def inputSize (rules : Array (PeriodicRule (Fin n) G)) : Nat :=
  n+rules.size+(rules.toList.map (fun r => r.premises.length)).sum+2

theorem quotient_size (rules : Array (PeriodicRule (Fin n) G)) :
    Indexed.inputSize (quotient rules)=inputSize rules := by
  simp [Indexed.inputSize,Indexed.premiseCount,quotient,inputSize,PeriodicRule.erase,List.map_map,Function.comp_def]

-- Erasing the offset fields and building the quotient's rule/premise lists.
def totalCost (rules : Array (PeriodicRule (Fin n) G)) : Nat :=
  8*inputSize rules+Indexed.totalCost (quotient rules)

theorem linear_time (rules : Array (PeriodicRule (Fin n) G)) : totalCost rules ≤ 72*inputSize rules := by
  have bound := Indexed.linear_time (quotient rules)
  rw [quotient_size] at bound
  unfold totalCost
  omega

variable [AddGroup G]

theorem check_correct (rules : Array (PeriodicRule (Fin n) G)) :
    check rules=true ↔ PeriodicSatisfiable rules.toList := by
  rw [check,Indexed.check_correct,periodic_satisfiable_iff]
  simp [quotient]

theorem dualCheck_correct (rules : Array (PeriodicRule (Fin n) G)) :
    check rules=true ↔ PeriodicDualSatisfiable rules.toList :=
  (check_correct rules).trans (dual_satisfiable_iff rules.toList).symm

theorem model_correct (rules : Array (PeriodicRule (Fin n) G)) (accepted : check rules=true) :
    PeriodicSatisfies rules.toList (fun a _ => model rules a=true) := by
  apply (constant_satisfies_iff rules.toList _).mpr
  have h := Indexed.model_correct (quotient rules) accepted
  simpa [quotient,model] using h

theorem dualModel_correct (rules : Array (PeriodicRule (Fin n) G)) (accepted : check rules=true) :
    PeriodicDualSatisfies rules.toList (fun a _ => (!model rules a)=true) := by
  have h := model_correct rules accepted
  simpa only [PeriodicDualSatisfies,Bool.not_eq_true',Bool.not_eq_false] using h

/-- Both periodic problems have correct period-one models and a linear RAM budget. -/
theorem certified (rules : Array (PeriodicRule (Fin n) G)) :
    (check rules=true ↔ PeriodicSatisfiable rules.toList) ∧
    (check rules=true ↔ PeriodicDualSatisfiable rules.toList) ∧
    totalCost rules ≤ 72*inputSize rules :=
  ⟨check_correct rules,dualCheck_correct rules,linear_time rules⟩

end LeanTrominoes.Horn.PeriodicIndexed

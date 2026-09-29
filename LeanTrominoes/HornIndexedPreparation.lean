/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornIndexedInput

/-! # Costed traversal from dense Horn rule arrays to premise occurrences

The counters below count RAM operations, not the cost of computing the counters
as extra output. Every input rule and every premise-list cell is visited.
-/
namespace LeanTrominoes.Horn.Indexed
variable {n : Nat} (input : Input n)

def emitPremises (r : RuleId input) : List (Fin n) → List (Option (Fin n) × RuleId input) × Nat
  | [] => ([],1)
  | a::as =>
    let rest := emitPremises r as
    ((some a,r)::rest.1,6+rest.2)

theorem emitPremises_value (r : RuleId input) (as : List (Fin n)) :
    (emitPremises input r as).1=as.map (fun a => (some a,r)) := by
  induction as <;> simp_all [emitPremises]

theorem emitPremises_cost (r : RuleId input) (as : List (Fin n)) :
    (emitPremises input r as).2=6*as.length+1 := by
  induction as <;> simp_all [emitPremises] <;> omega

def emitRules : List (RuleId input) → List (Option (Fin n) × RuleId input) × Nat
  | [] => ([],1)
  | r::rs =>
    let first := emitPremises input r input.rules[r].premises
    let rest := emitRules rs
    (first.1++rest.1,6+first.2+2*first.1.length+rest.2)

theorem emitRules_value (ids : List (RuleId input)) :
    (emitRules input ids).1=ids.flatMap (fun r => input.rules[r].premises.map (fun a => (some a,r))) := by
  induction ids <;> simp_all [emitRules,emitPremises_value]

theorem emitRules_cost (ids : List (RuleId input)) :
    (emitRules input ids).2=7*ids.length+8*(emitRules input ids).1.length+1 := by
  induction ids with
  | nil => simp [emitRules]
  | cons r rs ih =>
    simp only [emitRules,emitPremises_cost,emitPremises_value,List.length_append,List.length_map,List.length_cons] at *
    omega

def preparationSteps : Nat := 4*input.rules.size+1+(emitRules input (List.finRange input.rules.size)).2

theorem preparation_correct : (emitRules input (List.finRange input.rules.size)).1=edges input :=
  emitRules_value input _

theorem preparation_bound : preparationSteps input ≤ 16*(input.rules.size+premiseCount input+1) := by
  simp only [preparationSteps,emitRules_cost,preparation_correct,edges_length,List.length_finRange]
  omega

end LeanTrominoes.Horn.Indexed

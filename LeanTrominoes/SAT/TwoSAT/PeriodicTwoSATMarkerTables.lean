/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATMarkers
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBatchTables

/-! # Dense Horn tables after appending empty-clause markers

Lifting the old variables preserves their numeric codes. The appended marker
heads are the new dummy variable or zero; markers have no premise occurrences.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open ImplicationGraph.TwoSATBatch
variable {v n p : ℕ}

theorem ruleHeads_liftRule (rs : List (Horn.Rule (Fin v))) :
    ruleHeads (rs.map liftRule)=ruleHeads rs := by
  simp only [ruleHeads,List.map_map]
  apply List.map_congr_left
  intro r _
  cases h : r.conclusion <;> simp [liftRule,Horn.WordRAM.atomCode,h]

theorem occurrenceRulesFrom_liftRule (offset : ℕ) (rs : List (Horn.Rule (Fin v))) :
    occurrenceRulesFrom offset (rs.map liftRule)=occurrenceRulesFrom offset rs := by
  simp [occurrenceRulesFrom,List.zipIdx_map,List.flatMap_map,liftRule]

theorem occurrenceRulesFrom_markers (offset : ℕ) (flags : List Bool) :
    occurrenceRulesFrom offset (flags.map (marker v))=[] := by
  rw [occurrenceRulesFrom_uniform offset 0]
  · simp
  · intro r hr
    obtain ⟨flag,_,rfl⟩ := List.mem_map.mp hr
    rfl

theorem appendMarkers_heads (input : Horn.Indexed.Input v) (flags : List Bool) :
    ruleHeads (appendMarkers input flags).rules.toList=
      ruleHeads input.rules.toList++flags.map (fun flag => if flag then v+1 else 0) := by
  rw [show (appendMarkers input flags).rules.toList=
      input.rules.toList.map liftRule++flags.map (marker v) by simp [appendMarkers]]
  simp only [ruleHeads,List.map_append]
  rw [show (input.rules.toList.map liftRule).map (fun r => Horn.WordRAM.atomCode r.conclusion)=
    ruleHeads input.rules.toList from ruleHeads_liftRule _]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro flag _
  cases flag <;> simp [marker,Horn.WordRAM.atomCode]

theorem appendMarkers_ruleIds (input : Horn.Indexed.Input v) (flags : List Bool) :
    occurrenceRules (appendMarkers input flags).rules.toList=occurrenceRules input.rules.toList := by
  change occurrenceRulesFrom 0 (appendMarkers input flags).rules.toList=_
  simp only [appendMarkers,List.toList_toArray]
  rw [occurrenceRulesFrom_append,occurrenceRulesFrom_liftRule,occurrenceRulesFrom_markers,List.append_nil]
  rfl

/-- Adding markers changes only the variable/rule headers and appended heads. -/
theorem words_appendMarkers (input : Horn.Indexed.Input v) (flags : List Bool) :
    Horn.WordRAM.words ⟨v+1,appendMarkers input flags⟩=
      [v+1,input.rules.size+flags.length,(occurrenceAtoms input.rules.toList).length]++
      ruleHeads input.rules.toList++flags.map (fun flag => if flag then v+1 else 0)++
      occurrenceAtoms input.rules.toList++occurrenceRules input.rules.toList := by
  have eq := words_of_rules (appendMarkers input flags).rules.toList
  rw [appendMarkers_heads,appendMarkers_atoms,appendMarkers_ruleIds] at eq
  simpa only [Array.toArray_toList,Array.length_toList,appendMarkers_rules,List.append_assoc] using eq

/-- The complete marked batch encoding has explicit table formulas in every region. -/
theorem words_marked_batch (edges : List (Fin n × Fin n)) (pairs : Fin p → Fin n × Fin n)
    (flags : List Bool) :
    Horn.WordRAM.words ⟨p*2*n+1,appendMarkers (input edges pairs) flags⟩=
      [p*2*n+1,3*p+2*p*edges.length+flags.length,2*p+2*p*edges.length]++
      factHeads pairs++List.replicate p 0++edgeHeads (p:=p) edges++
      flags.map (fun flag => if flag then p*2*n+1 else 0)++
      negativeAtoms pairs++edgeAtoms (p:=p) edges++negativeRuleIds p++edgeRuleIds p edges.length := by
  have atomsLength : (occurrenceAtoms (input edges pairs).rules.toList).length=2*p+2*p*edges.length := by
    change (occurrenceAtoms (denseRules edges pairs)).length=_
    rw [occurrenceAtoms_batch]
    simp [negativeAtoms,edgeAtoms]
    ring
  rw [words_appendMarkers,atomsLength]
  change _++ruleHeads (denseRules edges pairs)++_++occurrenceAtoms (denseRules edges pairs)++
    occurrenceRules (denseRules edges pairs)=_
  rw [ruleHeads_batch,occurrenceAtoms_batch,occurrenceRules_batch]
  simp [input,denseRules,rules_length,negativeAtoms,edgeAtoms,
    Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,List.append_assoc]

end LeanTrominoes.PeriodicTwoSAT.WordRAM

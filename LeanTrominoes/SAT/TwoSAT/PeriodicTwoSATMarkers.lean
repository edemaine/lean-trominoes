/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FiniteTwoSATEncoding
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATPaddedCover

/-! # Horn marker rules for empty input clauses

Every clause contributes one marker. A nonempty clause contributes a harmless
fact on a new unused variable; an empty clause contributes a negative fact.
Thus fixed-length clause records need no filtering or preliminary answer.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM

variable {v : ℕ}

def liftRule (rule : Horn.Rule (Fin v)) : Horn.Rule (Fin (v+1)) :=
  ⟨rule.premises.map Fin.castSucc,rule.conclusion.map Fin.castSucc⟩

def marker (v : ℕ) (valid : Bool) : Horn.Rule (Fin (v+1)) :=
  ⟨[],if valid then some (Fin.last v) else none⟩

def appendMarkers (input : Horn.Indexed.Input v) (flags : List Bool) : Horn.Indexed.Input (v+1) :=
  ⟨(input.rules.toList.map liftRule++flags.map (marker v)).toArray⟩

theorem liftRule_holds (rule : Horn.Rule (Fin v)) (model : Fin (v+1) → Prop) :
    (liftRule rule).Holds model ↔ rule.Holds (fun a => model a.castSucc) := by
  simp only [liftRule,Horn.Rule.Holds,List.forall_mem_map]
  cases rule.conclusion <;> rfl

theorem appendMarkers_correct (input : Horn.Indexed.Input v) (flags : List Bool) :
    Horn.Satisfiable (appendMarkers input flags).rules.toList ↔
      Horn.Satisfiable input.rules.toList ∧ ∀ flag ∈ flags, flag=true := by
  constructor
  · rintro ⟨model,satisfied⟩
    constructor
    · refine ⟨fun a => model a.castSucc,?_⟩
      intro rule member
      apply (liftRule_holds rule model).mp
      exact satisfied _ (by simp only [appendMarkers,List.toList_toArray,List.mem_append]; exact Or.inl (List.mem_map.mpr ⟨rule,member,rfl⟩))
    · intro flag member
      cases flag with
      | false =>
        exact False.elim (satisfied (marker v false) (by simp [appendMarkers,member]) (by simp [marker]))
      | true => rfl
  · rintro ⟨⟨model,satisfied⟩,flagsTrue⟩
    let extended : Fin (v+1) → Prop := Fin.lastCases True model
    refine ⟨extended,?_⟩
    intro rule member
    simp only [appendMarkers,List.toList_toArray,List.mem_append,List.mem_map] at member
    rcases member with ⟨original,member,rfl⟩ | ⟨flag,member,rfl⟩
    · apply (liftRule_holds original extended).mpr
      simpa only [extended,Fin.lastCases_castSucc] using satisfied original member
    · rw [flagsTrue flag member]
      simp [marker,Horn.Rule.Holds,extended]

theorem appendMarkers_rules (input : Horn.Indexed.Input v) (flags : List Bool) :
    (appendMarkers input flags).rules.size=input.rules.size+flags.length := by simp [appendMarkers]

theorem appendMarkers_atoms (input : Horn.Indexed.Input v) (flags : List Bool) :
    ImplicationGraph.TwoSATBatch.occurrenceAtoms (appendMarkers input flags).rules.toList=
      ImplicationGraph.TwoSATBatch.occurrenceAtoms input.rules.toList := by
  simp [appendMarkers,ImplicationGraph.TwoSATBatch.occurrenceAtoms,List.flatMap_append,List.flatMap_map,
    liftRule,marker,List.map_map,Function.comp_def]

theorem appendMarkers_occurrences (input : Horn.Indexed.Input v) (flags : List Bool) :
    (Horn.Indexed.edges (appendMarkers input flags)).length=(Horn.Indexed.edges input).length := by
  rw [Horn.Indexed.edges_length,Horn.Indexed.edges_length]
  simp [Horn.Indexed.premiseCount,appendMarkers,liftRule,marker,List.map_map,Function.comp_def]

end LeanTrominoes.PeriodicTwoSAT.WordRAM

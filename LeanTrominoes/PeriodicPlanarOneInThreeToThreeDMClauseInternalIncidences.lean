/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMFixedRedIncidences

/-!
# Clause-internal incidences in the planar periodic 3DM assembly

The red, green, and blue internal elements of each clause prototype
correspond to the left, right, and bottom internal elements of Figure 5.
Their global incidence lists are exactly the respective three local
neighbors.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- Variable modules cannot meet a clause-internal element. -/
theorem occurrenceBlock_redClauseInternal_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : Variable × OccurrenceSlot) (clauseIndex : Nat) :
    (occurrenceTriples source entry.1 entry.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  cases kindEq :
      occurrenceConnectorKind source entry.1 entry.2 <;>
    simp [occurrenceTriples, kindEq, allOrdinaryTriples,
      allFixedRedTriples, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement, redClauseTerminal]

theorem occurrenceBlock_greenClauseInternal_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : Variable × OccurrenceSlot) (clauseIndex : Nat) :
    (occurrenceTriples source entry.1 entry.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  cases kindEq :
      occurrenceConnectorKind source entry.1 entry.2 <;>
    simp [occurrenceTriples, kindEq, allOrdinaryTriples,
      allFixedRedTriples, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryGreenElement, fixedRedGreenElement, greenClauseTerminal]

theorem occurrenceBlock_blueClauseInternal_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : Variable × OccurrenceSlot) (clauseIndex : Nat) :
    (occurrenceTriples source entry.1 entry.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  cases kindEq :
      occurrenceConnectorKind source entry.1 entry.2 <;>
    simp [occurrenceTriples, kindEq, allOrdinaryTriples,
      allFixedRedTriples, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryBlueElement, fixedRedBlueElement, blueClauseTerminal]

/-- The complete variable-module list contributes no clause-internal
incidences. -/
theorem variableTriples_redClauseInternal_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    (variableTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [occurrenceBlock_redClauseInternal_filterMap_nil]

theorem variableTriples_greenClauseInternal_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    (variableTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [occurrenceBlock_greenClauseInternal_filterMap_nil]

theorem variableTriples_blueClauseInternal_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) :
    (variableTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [occurrenceBlock_blueClauseInternal_filterMap_nil]

/-- One clause block contributes the red/left internal neighbor list exactly
at the selected clause index. -/
theorem clauseBlock_redInternal_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (current target : Nat) :
    (allClauseSets.map
        (Triple.clause (Variable := Variable) current)).filterMap
        (fun triple =>
          let reference :=
            (tripleReferences source triple).red
          if reference.atom = RedElement.clauseInternal target then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) =
      if current = target then
        (X3CClauseInternal.neighbors .left).map fun set =>
          ⟨.clause target set, (0, 0)⟩
      else [] := by
  by_cases same : current = target
  · subst current
    simp [allClauseSets, tripleReferences, clauseTripleReferences,
      clauseRedElement, X3CClauseSet.coloredReferences,
      X3CClauseInternal.neighbors]
  · simp [allClauseSets, tripleReferences, clauseTripleReferences,
      clauseRedElement, X3CClauseSet.coloredReferences, same]

theorem clauseBlock_greenInternal_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (current target : Nat) :
    (allClauseSets.map
        (Triple.clause (Variable := Variable) current)).filterMap
        (fun triple =>
          let reference :=
            (tripleReferences source triple).green
          if reference.atom = GreenElement.clauseInternal target then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) =
      if current = target then
        (X3CClauseInternal.neighbors .right).map fun set =>
          ⟨.clause target set, (0, 0)⟩
      else [] := by
  by_cases same : current = target
  · subst current
    simp [allClauseSets, tripleReferences, clauseTripleReferences,
      clauseGreenElement, X3CClauseSet.coloredReferences,
      X3CClauseInternal.neighbors]
  · simp [allClauseSets, tripleReferences, clauseTripleReferences,
      clauseGreenElement, X3CClauseSet.coloredReferences, same]

theorem clauseBlock_blueInternal_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (current target : Nat) :
    (allClauseSets.map
        (Triple.clause (Variable := Variable) current)).filterMap
        (fun triple =>
          let reference :=
            (tripleReferences source triple).blue
          if reference.atom = BlueElement.clauseInternal target then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) =
      if current = target then
        (X3CClauseInternal.neighbors .bottom).map fun set =>
          ⟨.clause target set, (0, 0)⟩
      else [] := by
  by_cases same : current = target
  · subst current
    simp [allClauseSets, tripleReferences, clauseTripleReferences,
      clauseBlueElement, X3CClauseSet.coloredReferences,
      X3CClauseInternal.neighbors]
  · simp [allClauseSets, tripleReferences, clauseTripleReferences,
      clauseBlueElement, X3CClauseSet.coloredReferences, same]

/-- Each colored clause-internal element exposes its three local neighbors
in the global presentation. -/
theorem problem_redIncidences_clauseInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    (problem source).redIncidences
        (.clauseInternal clauseIndex) =
      (X3CClauseInternal.neighbors .left).map fun set =>
        ⟨.clause clauseIndex set, (0, 0)⟩ := by
  rw [TypedProblem.redIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    variableTriples_redClauseInternal_filterMap_nil,
    List.nil_append, clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [show ∀ current,
      (allClauseSets.map
        (Triple.clause (Variable := Variable) current)).filterMap
          (fun triple =>
            let reference := (tripleReferences source triple).red
            if reference.atom =
                RedElement.clauseInternal clauseIndex then
              some (⟨triple, reference.offset⟩ : Incidence Variable)
            else none) =
        if current = clauseIndex then
          (X3CClauseInternal.neighbors .left).map fun set =>
            ⟨.clause clauseIndex set, (0, 0)⟩
        else [] by
      intro current
      simpa using
        (clauseBlock_redInternal_filterMap
          source current clauseIndex)]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (List.range source.clauses.length) clauseIndex
      ((X3CClauseInternal.neighbors .left).map fun set =>
        (⟨.clause clauseIndex set, (0, 0)⟩ :
          Incidence Variable))
      List.nodup_range (List.mem_range.mpr indexLt)

theorem problem_greenIncidences_clauseInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    (problem source).greenIncidences
        (.clauseInternal clauseIndex) =
      (X3CClauseInternal.neighbors .right).map fun set =>
        ⟨.clause clauseIndex set, (0, 0)⟩ := by
  rw [TypedProblem.greenIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom = GreenElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    variableTriples_greenClauseInternal_filterMap_nil,
    List.nil_append, clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [show ∀ current,
      (allClauseSets.map
        (Triple.clause (Variable := Variable) current)).filterMap
          (fun triple =>
            let reference := (tripleReferences source triple).green
            if reference.atom =
                GreenElement.clauseInternal clauseIndex then
              some (⟨triple, reference.offset⟩ : Incidence Variable)
            else none) =
        if current = clauseIndex then
          (X3CClauseInternal.neighbors .right).map fun set =>
            ⟨.clause clauseIndex set, (0, 0)⟩
        else [] by
      intro current
      simpa using
        (clauseBlock_greenInternal_filterMap
          source current clauseIndex)]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (List.range source.clauses.length) clauseIndex
      ((X3CClauseInternal.neighbors .right).map fun set =>
        (⟨.clause clauseIndex set, (0, 0)⟩ :
          Incidence Variable))
      List.nodup_range (List.mem_range.mpr indexLt)

theorem problem_blueIncidences_clauseInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    (problem source).blueIncidences
        (.clauseInternal clauseIndex) =
      (X3CClauseInternal.neighbors .bottom).map fun set =>
        ⟨.clause clauseIndex set, (0, 0)⟩ := by
  rw [TypedProblem.blueIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.clauseInternal clauseIndex then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    variableTriples_blueClauseInternal_filterMap_nil,
    List.nil_append, clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [show ∀ current,
      (allClauseSets.map
        (Triple.clause (Variable := Variable) current)).filterMap
          (fun triple =>
            let reference := (tripleReferences source triple).blue
            if reference.atom =
                BlueElement.clauseInternal clauseIndex then
              some (⟨triple, reference.offset⟩ : Incidence Variable)
            else none) =
        if current = clauseIndex then
          (X3CClauseInternal.neighbors .bottom).map fun set =>
            ⟨.clause clauseIndex set, (0, 0)⟩
        else [] by
      intro current
      simpa using
        (clauseBlock_blueInternal_filterMap
          source current clauseIndex)]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (List.range source.clauses.length) clauseIndex
      ((X3CClauseInternal.neighbors .bottom).map fun set =>
        (⟨.clause clauseIndex set, (0, 0)⟩ :
          Incidence Variable))
      List.nodup_range (List.mem_range.mpr indexLt)

/-- The three colored clause-internal elements have degree three. -/
theorem clauseInternal_degrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    ((problem source).redIncidences
        (.clauseInternal clauseIndex)).length = 3 ∧
      ((problem source).greenIncidences
        (.clauseInternal clauseIndex)).length = 3 ∧
      ((problem source).blueIncidences
        (.clauseInternal clauseIndex)).length = 3 := by
  rw [problem_redIncidences_clauseInternal source clauseIndex indexLt,
    problem_greenIncidences_clauseInternal source clauseIndex indexLt,
    problem_blueIncidences_clauseInternal source clauseIndex indexLt]
  simp [X3CClauseInternal.neighbors]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

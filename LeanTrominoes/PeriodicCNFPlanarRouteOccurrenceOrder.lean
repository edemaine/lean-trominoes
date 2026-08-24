/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableSiteOccurrenceData
import Mathlib.Data.List.Sort

/-! # Presentation order of routed periodic-CNF occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

private def routeOccurrencesFrom
    {Variable : Type*}
    (incidences : List (CNFIncidence Variable)) (start : Nat) :
    List (CNFRouteOccurrence Variable) :=
  (incidences.zipIdx start).flatMap fun taggedIncidence =>
    neighborTranslations.map fun translate =>
      ⟨taggedIncidence.1, taggedIncidence.2, translate⟩

private theorem le_snd_of_mem_zipIdx
    {Value : Type*} {values : List Value} {start : Nat}
    {tagged : Value × Nat}
    (taggedMember : tagged ∈ values.zipIdx start) :
    start ≤ tagged.2 := by
  induction values generalizing start with
  | nil => simp at taggedMember
  | cons value values induction =>
      simp only [List.zipIdx_cons, List.mem_cons] at taggedMember
      rcases taggedMember with taggedEq | taggedMember
      · subst tagged
        rfl
      · exact le_trans (Nat.le_succ start)
          (by simpa [Nat.add_comm] using
            (induction (start := start + 1) taggedMember))

private theorem routeOccurrencesFrom_edgeIndex_ge
    {Variable : Type*}
    (incidences : List (CNFIncidence Variable)) (start : Nat)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ routeOccurrencesFrom incidences start) :
    start ≤ occurrence.edgeIndex := by
  unfold routeOccurrencesFrom at occurrenceMember
  rcases List.mem_flatMap.mp occurrenceMember with
    ⟨taggedIncidence, taggedMember, occurrenceMember⟩
  rcases List.mem_map.mp occurrenceMember with
    ⟨translate, _translateMember, occurrenceEq⟩
  subst occurrence
  exact le_snd_of_mem_zipIdx taggedMember

private theorem routeOccurrencesFrom_pairwise_edgeIndex
    {Variable : Type*}
    (incidences : List (CNFIncidence Variable)) (start : Nat) :
    (routeOccurrencesFrom incidences start).Pairwise fun first second =>
      first.edgeIndex ≤ second.edgeIndex := by
  induction incidences generalizing start with
  | nil => simp [routeOccurrencesFrom]
  | cons incidence incidences induction =>
      unfold routeOccurrencesFrom
      simp only [List.zipIdx_cons, List.flatMap_cons]
      rw [List.pairwise_append]
      refine ⟨?_, induction (start + 1), ?_⟩
      · apply List.pairwise_of_forall_mem_list
        intro first firstMember second secondMember
        rcases List.mem_map.mp firstMember with
          ⟨firstTranslate, _firstTranslateMember, firstEq⟩
        rcases List.mem_map.mp secondMember with
          ⟨secondTranslate, _secondTranslateMember, secondEq⟩
        subst first
        subst second
        rfl
      · intro first firstMember second secondMember
        rcases List.mem_map.mp firstMember with
          ⟨firstTranslate, _firstTranslateMember, firstEq⟩
        subst first
        exact Nat.le_trans (Nat.le_succ start)
          (routeOccurrencesFrom_edgeIndex_ge
            incidences (start + 1) secondMember)

/-- The neighboring occurrence enumeration is already nondecreasing by its
global incidence index. -/
theorem drawingCNFRouteOccurrences_pairwise_edgeIndex
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    (drawingCNFRouteOccurrences formula).Pairwise fun first second =>
      first.edgeIndex ≤ second.edgeIndex := by
  change
    (routeOccurrencesFrom
      (PeriodicCNF.incidencesWithMetadata formula) 0).Pairwise _
  exact routeOccurrencesFrom_pairwise_edgeIndex _ 0

/-- Selecting one variable site preserves incidence order, so its explicit
insertion sort is semantically inert. -/
theorem variableRouteOccurrencesAt_eq_filter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    variableRouteOccurrencesAt formula site =
      (drawingCNFRouteOccurrences formula).filter fun occurrence =>
        occurrence.variableOccurrence = site := by
  unfold variableRouteOccurrencesAt
  exact
    ((drawingCNFRouteOccurrences_pairwise_edgeIndex formula).filter _).insertionSort_eq

end LeanTrominoes.PeriodicOrthocrossing

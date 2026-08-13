/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteSoundness

/-!
# Degree bounds for routed CNF variable sites

For a fixed lifted variable site, each syntactic incidence contributes at
most one translated route: translation by a fixed edge offset is injective.
Consequently the routed occurrence list is bounded by the protovariable's
ordinary occurrence count in the finite periodic CNF presentation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Forgetting incidence metadata down to literal atoms recovers exactly the
source formula's variable-occurrence list. -/
theorem PeriodicCNF.incidencesWithMetadata_literal_atoms
    {Variable : Type*}
    (formula : PeriodicCNF Variable) :
    (PeriodicCNF.incidencesWithMetadata formula).map
        (fun incidence => incidence.literal.atom) =
      formula.variableOccurrences := by
  unfold PeriodicCNF.incidencesWithMetadata
    PeriodicCNF.variableOccurrences
  simp only [List.map_flatMap]
  rw [← PeriodicCNF.zipIdx_flatMap_fst
    (fun clause => clause.map PeriodicLiteral.atom)
    formula.clauses 0]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMem
  calc
    _ =
        ((taggedClause.1.zipIdx.map Prod.fst).map
          PeriodicLiteral.atom) := by
      simp only [List.map_map]
      rfl
    _ = _ := by
      rw [List.zipIdx_map_fst]

/-- Translations of one fixed incidence have pairwise distinct lifted
variable sites. -/
theorem translatedIncidenceVariableOccurrences_nodup
    {Variable : Type*} [DecidableEq Variable]
    (taggedIncidence : CNFIncidence Variable × Nat) :
    (neighborTranslations.map fun translate =>
      (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
        CNFRouteOccurrence Variable).variableOccurrence).Nodup := by
  apply List.Nodup.map
  · intro first second occurrenceEq
    have cellEq := congrArg Prod.snd occurrenceEq
    rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    simp only [CNFRouteOccurrence.variableOccurrence,
      CNFRouteOccurrence.edge, Cell.add] at cellEq
    injection cellEq with horizontalEq verticalEq
    exact Prod.ext
      (add_right_cancel horizontalEq)
      (add_right_cancel verticalEq)
  · exact neighborTranslations_nodup

/-- A noduplicated list whose every member equals one fixed value has length
at most one. -/
theorem length_le_one_of_nodup_of_forall_eq
    {Value : Type*} {values : List Value}
    (nodup : values.Nodup) (value : Value)
    (allEqual : ∀ item ∈ values, item = value) :
    values.length ≤ 1 := by
  cases values with
  | nil =>
      simp
  | cons first rest =>
      cases rest with
      | nil =>
          simp
      | cons second rest =>
          have firstNeSecond : first ≠ second := by
            intro firstEqSecond
            subst second
            exact (List.nodup_cons.mp nodup).1 (by simp)
          exact (firstNeSecond
            ((allEqual first (by simp)).trans
              (allEqual second (by simp)).symm)).elim

/-- At most one translation of a fixed metadata incidence reaches a fixed
lifted variable site. -/
theorem translatedIncidenceFilter_length_le_one
    {Variable : Type*} [DecidableEq Variable]
    (taggedIncidence : CNFIncidence Variable × Nat)
    (site : VariableRouteSite Variable) :
    ((neighborTranslations.map fun translate =>
        (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
          CNFRouteOccurrence Variable)).filter fun occurrence =>
            occurrence.variableOccurrence = site).length ≤ 1 := by
  let routes :=
    neighborTranslations.map fun translate =>
      (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
        CNFRouteOccurrence Variable)
  let filtered :=
    routes.filter fun occurrence =>
      occurrence.variableOccurrence = site
  calc
    filtered.length =
        (filtered.map
          CNFRouteOccurrence.variableOccurrence).length := by
      rw [List.length_map]
    _ ≤ 1 := by
      refine length_le_one_of_nodup_of_forall_eq ?_ site ?_
      · exact List.Nodup.sublist
          ((List.filter_sublist (l := routes)).map
            CNFRouteOccurrence.variableOccurrence)
          (translatedIncidenceVariableOccurrences_nodup
            taggedIncidence)
      · intro item itemMem
        rcases List.mem_map.mp itemMem with
          ⟨occurrence, occurrenceMem, itemEq⟩
        subst item
        exact of_decide_eq_true
          (List.mem_filter.mp occurrenceMem).2

/-- The routed copies of one fixed incidence contribute at most one route
to a site if their atom matches, and none otherwise. -/
theorem translatedIncidenceFilter_length_le_atomIndicator
    {Variable : Type*} [DecidableEq Variable]
    (taggedIncidence : CNFIncidence Variable × Nat)
    (site : VariableRouteSite Variable) :
    ((neighborTranslations.map fun translate =>
        (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
          CNFRouteOccurrence Variable)).filter fun occurrence =>
            occurrence.variableOccurrence = site).length ≤
      if taggedIncidence.1.literal.atom = site.1 then 1 else 0 := by
  by_cases sameAtom :
      taggedIncidence.1.literal.atom = site.1
  · simpa [sameAtom] using
      translatedIncidenceFilter_length_le_one
        taggedIncidence site
  · simp only [if_neg sameAtom, Nat.le_zero]
    rw [List.length_eq_zero_iff]
    rw [List.filter_eq_nil_iff]
    intro occurrence occurrenceMem
    rcases List.mem_map.mp occurrenceMem with
      ⟨translate, translateMem, occurrenceEq⟩
    subst occurrence
    intro reachesSite
    have siteEq :
        (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
          CNFRouteOccurrence Variable).variableOccurrence = site :=
      of_decide_eq_true reachesSite
    exact sameAtom (congrArg Prod.fst siteEq)

/-- Filtering all neighboring routed copies at one lifted variable site is
bounded by the number of matching metadata incidences. -/
theorem drawingVariableRouteOccurrences_length_le_metadata_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    ((drawingCNFRouteOccurrences formula).filter fun occurrence =>
        occurrence.variableOccurrence = site).length ≤
      (((PeriodicCNF.incidencesWithMetadata formula).zipIdx.map
        fun taggedIncidence =>
          taggedIncidence.1.literal.atom).count site.1) := by
  let taggedIncidences :=
    (PeriodicCNF.incidencesWithMetadata formula).zipIdx
  change
    ((taggedIncidences.flatMap fun taggedIncidence =>
      neighborTranslations.map fun translate =>
        (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
          CNFRouteOccurrence Variable)).filter fun occurrence =>
            occurrence.variableOccurrence = site).length ≤
      ((taggedIncidences.map fun taggedIncidence =>
        taggedIncidence.1.literal.atom).count site.1)
  induction taggedIncidences with
  | nil =>
      simp
  | cons taggedIncidence rest induction =>
      rw [List.flatMap_cons, List.filter_append,
        List.length_append, List.map_cons, List.count_cons]
      have firstLe :=
        translatedIncidenceFilter_length_le_atomIndicator
          taggedIncidence site
      by_cases sameAtom :
          taggedIncidence.1.literal.atom = site.1
      · simp only [sameAtom, beq_self_eq_true, if_true] at firstLe ⊢
        omega
      · have differentBeq :
            (taggedIncidence.1.literal.atom == site.1) = false := by
          exact Bool.eq_false_iff.mpr fun equal =>
            sameAtom (eq_of_beq equal)
        simp only [sameAtom, if_false, differentBeq] at firstLe ⊢
        omega

/-- The number of routed occurrences reaching a lifted variable site is at
most the source protovariable's occurrence count. -/
theorem variableRouteOccurrencesAt_length_le_occurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    (variableRouteOccurrencesAt formula site).length ≤
      formula.variableOccurrences.count site.1 := by
  rw [variableRouteOccurrencesAt, List.length_insertionSort]
  calc
    _ ≤
        (((PeriodicCNF.incidencesWithMetadata formula).zipIdx.map
          fun taggedIncidence =>
            taggedIncidence.1.literal.atom).count site.1) :=
      drawingVariableRouteOccurrences_length_le_metadata_count
        formula site
    _ =
        ((PeriodicCNF.incidencesWithMetadata formula).map
          fun incidence => incidence.literal.atom).count site.1 := by
      congr 1
      calc
        _ =
            (((PeriodicCNF.incidencesWithMetadata formula).zipIdx.map
              Prod.fst).map fun incidence =>
                incidence.literal.atom) := by
          rw [List.map_map]
          rfl
        _ = _ := by
          rw [List.zipIdx_map_fst]
    _ = formula.variableOccurrences.count site.1 := by
      rw [PeriodicCNF.incidencesWithMetadata_literal_atoms]

/-- A degree-three periodic CNF presentation produces at most three routed
occurrences at every lifted variable site. -/
theorem variableRouteOccurrencesAt_length_le_three
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (site : VariableRouteSite Variable) :
    (variableRouteOccurrencesAt formula site).length ≤ 3 :=
  (variableRouteOccurrencesAt_length_le_occurrences formula site).trans
    (occurrences site.1)

end PeriodicOrthocrossing
end LeanTrominoes

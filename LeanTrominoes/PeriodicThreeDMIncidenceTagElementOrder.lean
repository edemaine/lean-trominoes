/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicThreeDMGraph
import LeanTrominoes.ListGroupedFieldLookup

/-! # Filtering canonical incidence tags by their colored element -/

namespace LeanTrominoes.PeriodicThreeDM

open Gadget

/-- The colored element reached by a canonical incidence tag. -/
def incidenceElement (problem : PeriodicThreeDM) (tag : IncidenceTag) : WireColor × Nat :=
  (tag.color, ((problem.triples.getD tag.tripleIndex default).reference tag.color).atom)

/-- Filtering triple-major incidence tags preserves exactly the incidence
order at the selected colored element. No degree bound is required. -/
theorem incidenceTags_filter_element
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat) :
    (problem.incidenceTags.filter fun tag => decide (problem.incidenceElement tag = (color, atom))) =
      (problem.incidences color atom).map (fun incidence =>
        (⟨incidence.tripleIndex, color⟩ : IncidenceTag)) := by
  rw [incidenceTags_eq_range_flatMap]
  unfold incidences
  generalize List.range problem.triples.length = indices
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.filter_append, List.filterMap_cons]
      rw [induction]
      by_cases equal : ((problem.triples.getD index default).reference color).atom = atom
      · simp only [List.getD_eq_getElem?_getD] at equal
        cases color <;>
          simp [tripleIncidenceTags, incidenceColors, incidenceElement, equal]
      · simp only [List.getD_eq_getElem?_getD] at equal
        cases color <;>
          simp [tripleIncidenceTags, incidenceColors, incidenceElement, equal]


/-- Stable numeric grouping of aligned incidence fields is exactly grouping
by the actual colored element whenever the identity comparison agrees. -/
theorem incidenceFields_grouped_code_eq
    {Field : Type*} (problem : PeriodicThreeDM)
    (elements : List (WireColor × Nat)) (code : WireColor × Nat → Nat)
    (field : IncidenceTag → Field) (fallback : Field)
    (identified : ∀ element ∈ elements, ∀ tag ∈ problem.incidenceTags,
      code (problem.incidenceElement tag) = code element ↔
        problem.incidenceElement tag = element) :
    (elements.map code).flatMap (fun key =>
      ((problem.incidenceTags.map (fun tag => code (problem.incidenceElement tag))).idxsOf key).map
        (fun index => (problem.incidenceTags.map field).getD index fallback)) =
      elements.flatMap (fun element => (problem.incidences element.1 element.2).map
        (fun incidence => field ⟨incidence.tripleIndex, element.1⟩)) := by
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro element member
  rw [List.map_codeIndices_getD_eq_filter_map problem.incidenceTags
    (fun tag => code (problem.incidenceElement tag)) (code element)
    problem.incidenceElement element field fallback (identified element member)]
  rw [incidenceTags_filter_element problem element.1 element.2, List.map_map]
  rfl

end LeanTrominoes.PeriodicThreeDM

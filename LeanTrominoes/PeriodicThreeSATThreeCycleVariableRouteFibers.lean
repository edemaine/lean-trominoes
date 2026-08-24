/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapFilterSingleton
import LeanTrominoes.PeriodicCNFIncidenceMetadataSize
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceFiberSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceData

/-! # Cycle-link occurrence fibers at one variable site -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every explicit cycle-link incidence has zero normalized edge offset. -/
theorem cycleLinkIncidence_edge_offset_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {incidence : CNFIncidence (ThreeOccurrenceVariable Variable)}
    (incidenceMember : incidence ∈ cycleLinkIncidences source) :
    incidence.edge.offset = (0, 0) := by
  unfold cycleLinkIncidences at incidenceMember
  rcases List.mem_flatMap.mp incidenceMember with
    ⟨taggedLink, _taggedLinkMember, incidenceMember⟩
  unfold cycleLinkIncidenceBlock at incidenceMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at incidenceMember
  rcases incidenceMember with incidenceEq | incidenceEq
  · subst incidence
    rfl
  · subst incidence
    rfl

/-- At a neighboring zero-offset site, the cycle suffix contributes exactly
the matching cycle incidences in global order; outside it contributes none. -/
theorem cycleLinkIncidenceFibersAt_eq_filter_map
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable) (position : Cell) :
    ((cycleLinkIncidences source).zipIdx
          (PeriodicCNF.presentationLiteralCount source)).flatMap
        (fun taggedIncidence =>
          translatedIncidenceOccurrencesAt taggedIncidence
            (atom, position)) =
      if position ∈ neighborTranslations then
        (((cycleLinkIncidences source).zipIdx
            (PeriodicCNF.presentationLiteralCount source)).filter
          fun taggedIncidence =>
            taggedIncidence.1.literal.atom = atom).map
          fun taggedIncidence =>
            (⟨taggedIncidence.1, taggedIncidence.2, position⟩ :
              CNFRouteOccurrence (ThreeOccurrenceVariable Variable))
      else
        [] := by
  let taggedIncidences := (cycleLinkIncidences source).zipIdx
    (PeriodicCNF.presentationLiteralCount source)
  by_cases positionMember : position ∈ neighborTranslations
  · rw [if_pos positionMember]
    calc
      taggedIncidences.flatMap
          (fun taggedIncidence =>
            translatedIncidenceOccurrencesAt taggedIncidence
              (atom, position)) =
          taggedIncidences.flatMap (fun taggedIncidence =>
            if taggedIncidence.1.literal.atom = atom then
              [(⟨taggedIncidence.1, taggedIncidence.2, position⟩ :
                CNFRouteOccurrence (ThreeOccurrenceVariable Variable))]
            else []) := by
        apply List.flatMap_congr
        intro taggedIncidence taggedMember
        rw [translatedIncidenceOccurrencesAt_eq]
        have offsetZero := cycleLinkIncidence_edge_offset_eq_zero source
          (List.fst_mem_of_mem_zipIdx taggedMember)
        rw [offsetZero]
        simp [Cell.sub, positionMember]
      _ = _ := flatMap_if_singleton_eq_filter_map taggedIncidences
        (fun taggedIncidence => taggedIncidence.1.literal.atom) atom
        (fun taggedIncidence =>
          (⟨taggedIncidence.1, taggedIncidence.2, position⟩ :
            CNFRouteOccurrence (ThreeOccurrenceVariable Variable)))
  · rw [if_neg positionMember]
    rw [List.flatMap_eq_nil_iff]
    intro taggedIncidence taggedMember
    rw [translatedIncidenceOccurrencesAt_eq]
    have offsetZero := cycleLinkIncidence_edge_offset_eq_zero source
      (List.fst_mem_of_mem_zipIdx taggedMember)
    rw [offsetZero]
    simp [Cell.sub, positionMember]

end LeanTrominoes.PeriodicThreeSATThree

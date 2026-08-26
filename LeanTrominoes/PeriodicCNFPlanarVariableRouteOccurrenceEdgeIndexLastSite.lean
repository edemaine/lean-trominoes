/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOccurrences
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceFiberSemantics

/-! # A final neighboring site covers all routed edge indices -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- If every incidence stays in the current or next slice, every global
route index reaching any translated site of an atom also reaches that
atom's final neighboring site `(1,1)`. -/
theorem variableRouteOccurrenceEdgeIndices_subset_finalSite
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈
      PeriodicCNF.incidencesWithMetadata formula,
        incidence.edge.offset = (0, 0) ∨
          incidence.edge.offset = (1, 0))
    (atom : Variable) (position : Cell) :
    (variableRouteOccurrencesAt formula (atom, position)).map
        CNFRouteOccurrence.edgeIndex ⊆
      (variableRouteOccurrencesAt formula (atom, (1, 1))).map
        CNFRouteOccurrence.edgeIndex := by
  intro edgeIndex edgeIndexMember
  rcases List.mem_map.mp edgeIndexMember with
    ⟨occurrence, occurrenceMember, rfl⟩
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula (atom, position) occurrenceMember
  rcases List.mem_flatMap.mp occurrenceData.1 with
    ⟨taggedIncidence, taggedMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, occurrenceEq⟩
  subst occurrence
  have atomEq : taggedIncidence.1.literal.atom = atom := by
    simpa only [CNFRouteOccurrence.variableOccurrence]
      using congrArg Prod.fst occurrenceData.2
  let finalTranslate :=
    Cell.sub ((1, 1) : Cell) taggedIncidence.1.edge.offset
  have finalTranslateMember : finalTranslate ∈ neighborTranslations := by
    rcases positiveOffsets taggedIncidence.1
        (List.fst_mem_of_mem_zipIdx taggedMember) with
      offsetZero | offsetOne
    · change Cell.sub ((1, 1) : Cell)
          taggedIncidence.1.edge.offset ∈ neighborTranslations
      rw [offsetZero]
      native_decide
    · change Cell.sub ((1, 1) : Cell)
          taggedIncidence.1.edge.offset ∈ neighborTranslations
      rw [offsetOne]
      native_decide
  let finalOccurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, finalTranslate⟩
  have finalOccurrenceMember : finalOccurrence ∈
      variableRouteOccurrencesAt formula (atom, (1, 1)) := by
    rw [variableRouteOccurrencesAt_eq_flatMap_fibers]
    apply List.mem_flatMap.mpr
    refine ⟨taggedIncidence, taggedMember, ?_⟩
    rw [translatedIncidenceOccurrencesAt_eq, if_pos atomEq]
    rw [if_pos finalTranslateMember]
    exact List.mem_singleton.mpr rfl
  exact List.mem_map.mpr
    ⟨finalOccurrence, finalOccurrenceMember, rfl⟩

end PeriodicOrthocrossing
end LeanTrominoes

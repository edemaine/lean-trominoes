/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupFlatMapFinalBlock
import LeanTrominoes.PeriodicCNFPlanarDegree
import LeanTrominoes.PeriodicCNFPlanarVariableRouteOccurrenceEdgeIndexLastSite
import LeanTrominoes.PeriodicCNFPlanarVariableRouteOccurrenceEdgeIndexNodup
import LeanTrominoes.PeriodicCNFPlanarVariableRouteSiteBlocks

/-! # Deduplicating one translated routed-variable edge-index block -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Route indices selected throughout one complete zero-offset neighboring
site block. -/
def routedVariableSiteEdgeIndexBlock
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable) : List Nat :=
  (variableRouteSiteBlock atom (0, 0)).flatMap fun site =>
    ((variableRouteOccurrencesAt formula site).take 3).map
      CNFRouteOccurrence.edgeIndex

/-- The complete final-site fiber of one atom. -/
def routedVariableFinalSiteEdgeIndexBlock
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (atom : Variable) : List Nat :=
  ((variableRouteOccurrencesAt formula (atom, (1, 1))).take 3).map
    CNFRouteOccurrence.edgeIndex

/-- Stable deduplication of a nine-site translated block retains exactly
its duplicate-free final-site route-index fiber. -/
theorem routedVariableSiteEdgeIndexBlock_dedup_eq_final
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈
      PeriodicCNF.incidencesWithMetadata formula,
        incidence.edge.offset = (0, 0) ∨
          incidence.edge.offset = (1, 0))
    (occurrences : formula.OccurrencesAtMost 3)
    (atom : Variable) :
    (routedVariableSiteEdgeIndexBlock formula atom).dedup =
      routedVariableFinalSiteEdgeIndexBlock formula atom := by
  let block := fun position : Cell =>
    ((variableRouteOccurrencesAt formula (atom, position)).take 3).map
      CNFRouteOccurrence.edgeIndex
  have translationsEq : neighborTranslations =
      neighborTranslations.dropLast ++ [((1, 1) : Cell)] := by
    native_decide
  unfold routedVariableSiteEdgeIndexBlock
    routedVariableFinalSiteEdgeIndexBlock
  rw [variableRouteSiteBlock, List.flatMap_map]
  change (neighborTranslations.flatMap block).dedup = block (1, 1)
  rw [translationsEq]
  apply List.dedup_flatMap_append_singleton_eq_final
  · intro position _positionMember
    unfold block
    have positionTake :
        (variableRouteOccurrencesAt formula (atom, position)).take 3 =
          variableRouteOccurrencesAt formula (atom, position) :=
      (List.take_eq_self_iff _).mpr
        (variableRouteOccurrencesAt_length_le_three
          formula occurrences (atom, position))
    have finalTake :
        (variableRouteOccurrencesAt formula (atom, (1, 1))).take 3 =
          variableRouteOccurrencesAt formula (atom, (1, 1)) :=
      (List.take_eq_self_iff _).mpr
        (variableRouteOccurrencesAt_length_le_three
          formula occurrences (atom, (1, 1)))
    rw [positionTake, finalTake]
    exact variableRouteOccurrenceEdgeIndices_subset_finalSite
      formula positiveOffsets atom position
  · unfold block
    have finalTake :
        (variableRouteOccurrencesAt formula (atom, (1, 1))).take 3 =
          variableRouteOccurrencesAt formula (atom, (1, 1)) :=
      (List.take_eq_self_iff _).mpr
        (variableRouteOccurrencesAt_length_le_three
          formula occurrences (atom, (1, 1)))
    rw [finalTake]
    exact variableRouteOccurrencesAt_edgeIndices_nodup
      formula (atom, (1, 1))

end PeriodicOrthocrossing
end LeanTrominoes

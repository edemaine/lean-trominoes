/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupRepeatedDisjointBlocks
import LeanTrominoes.PeriodicCNFPlanarVariableRouteSiteEdgeIndexBlockDisjointness
import LeanTrominoes.PeriodicThreeSATThreeCycleVariableRouteFibers
import LeanTrominoes.PeriodicThreeSATThreeRotatedOccurrenceVariablesBasic
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteSiteOrder

/-! # Deduplicated edge indices of rotated occurrence-site blocks -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- All incidences of the split formula have current/next-slice offsets
when the copied-incidence prefix does. -/
theorem formula_incidencesWithMetadata_offsets_zero_or_one
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    ∀ incidence ∈ PeriodicCNF.incidencesWithMetadata (formula source),
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0) := by
  intro incidence incidenceMember
  rw [formula_incidencesWithMetadata_eq_occurrence_append_cycle]
    at incidenceMember
  rcases List.mem_append.mp incidenceMember with
    occurrenceMember | cycleMember
  · exact positiveOffsets incidence occurrenceMember
  · have cycleLinkMember : incidence ∈ cycleLinkIncidences source := by
      rw [cycleLinkIncidences_eq_cycleIncidences]
      exact cycleMember
    exact Or.inl
      (cycleLinkIncidence_edge_offset_eq_zero source cycleLinkMember)

/-- The split formula's three-occurrence bound under the decidable-equality
implementation used by routed metadata. -/
theorem formula_occurrencesAtMostThree_decidableEq
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    @PeriodicCNF.OccurrencesAtMost
      (ThreeOccurrenceVariable Variable)
      (@instBEqOfDecidableEq
        (ThreeOccurrenceVariable Variable)
        (inferInstance : DecidableEq
          (ThreeOccurrenceVariable Variable)))
      (by infer_instance) 3 (formula source) := by
  apply PeriodicCNF.occurrencesAtMost_congr_beq
  exact formula_occurrencesAtMostThree source

/-- Canonical route-index representatives: the complete final-site fiber
of each occurrence atom in rotated target order. -/
def canonicalRoutedVariableEdgeIndexScan
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  (rotatedOccurrenceVariables source).flatMap
    (routedVariableFinalSiteEdgeIndexBlock (formula source))

/-- Stable deduplication of all rotated nine-site blocks retains one
complete final-site route-index fiber per occurrence atom. -/
theorem rotatedVariableRouteSiteBlocks_edgeIndices_dedup_eq_canonical
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    (((rotatedVariableRouteSiteBlocks source).flatMap fun site =>
        ((variableRouteOccurrencesAt (formula source) site).take 3).map
          CNFRouteOccurrence.edgeIndex).dedup) =
      canonicalRoutedVariableEdgeIndexScan source := by
  have blocksDisjoint : (rotatedOccurrenceVariables source).Pairwise
      (fun first second => List.Disjoint
        (routedVariableSiteEdgeIndexBlock (formula source) first)
        (routedVariableSiteEdgeIndexBlock (formula source) second)) := by
    apply (rotatedOccurrenceVariables_nodup source).pairwise_of_forall_ne
    intro first _firstMember second _secondMember different
    exact routedVariableSiteEdgeIndexBlock_disjoint_of_atom_ne
      (formula source) different
  unfold rotatedVariableRouteSiteBlocks
    canonicalRoutedVariableEdgeIndexScan
  rw [List.flatMap_assoc]
  change ((rotatedOccurrenceVariables source).flatMap
      (routedVariableSiteEdgeIndexBlock (formula source))).dedup = _
  rw [List.dedup_flatMap_pairwise_disjoint _ _ blocksDisjoint]
  apply List.flatMap_congr
  intro atom _atomMember
  exact routedVariableSiteEdgeIndexBlock_dedup_eq_final
    (formula source)
    (formula_incidencesWithMetadata_offsets_zero_or_one
      source positiveOffsets)
    (formula_occurrencesAtMostThree_decidableEq source)
    atom

end PeriodicThreeSATThree
end LeanTrominoes

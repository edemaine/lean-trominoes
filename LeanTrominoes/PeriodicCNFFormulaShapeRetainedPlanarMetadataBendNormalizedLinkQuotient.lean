/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupRepeatedDisjointBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedLinkGeometry
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorBendEnumeration
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEdgeIndexNodup

/-! # Quotienting normalized retained-bend links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Mapping the semantic bend-link enumeration through wrapped normalization
exposes the numeric route-major neighboring-translation blocks. -/
theorem drawingRouteBendLinks_wrappedNormalized_eq_neighborBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (drawingRouteBendLinks source.incidenceGraph).map
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source)) =
      (numericRouteDescriptors source).flatMap fun descriptor =>
        neighborTranslations.flatMap fun translate =>
          translatedRouteBendNormalizedLinks
            source descriptor translate := by
  unfold drawingRouteBendLinks
  rw [incidenceGraph_drawingRouteBends_dedup,
    incidenceGraph_drawingRouteBends_eq_numeric]
  simp only [List.map_flatMap, List.map_map,
    translatedRouteBendNormalizedLinks,
    Function.comp_def]
  rfl

/-- The neighboring normalized bend-link blocks of distinct numeric routes
are disjoint. -/
theorem neighborRouteBendNormalizedLinks_disjoint_of_edgeIndex_ne
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : RouteDescriptor)
    (edgeIndexNe : first.edgeIndex ≠ second.edgeIndex) :
    List.Disjoint
      (neighborTranslations.flatMap fun translate =>
        translatedRouteBendNormalizedLinks source first translate)
      (neighborTranslations.flatMap fun translate =>
        translatedRouteBendNormalizedLinks source second translate) := by
  rw [List.disjoint_left]
  intro link firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstTranslate, _firstTranslateMember, firstMember⟩
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondTranslate, _secondTranslateMember, secondMember⟩
  exact
    (translatedRouteBendNormalizedLinks_disjoint_of_edgeIndex_ne
      source first second edgeIndexNe
      firstTranslate secondTranslate) firstMember secondMember

/-- Deduplicating the nine normalized occurrences of one route retains its
single untranslated block. -/
theorem neighborRouteBendNormalizedLinks_dedup_eq_base
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (descriptor : RouteDescriptor) :
    (neighborTranslations.flatMap fun translate =>
      translatedRouteBendNormalizedLinks
        source descriptor translate).dedup =
      translatedRouteBendNormalizedLinks
        source descriptor (0, 0) := by
  have blocksEq :
      (neighborTranslations.flatMap fun translate =>
        translatedRouteBendNormalizedLinks source descriptor translate) =
        (neighborTranslations.flatMap fun _ =>
          translatedRouteBendNormalizedLinks
            source descriptor (0, 0)) := by
    apply List.flatMap_congr
    intro translate _translateMember
    exact translatedRouteBendNormalizedLinks_eq_base
      source descriptor translate
  rw [blocksEq,
    List.dedup_flatMap_const_of_nonempty
      neighborTranslations
      (translatedRouteBendNormalizedLinks
        source descriptor (0, 0)) (by
          simp [neighborTranslations, neighborCoordinates])]
  exact List.dedup_eq_self.mpr
    (translatedRouteBendNormalizedLinks_nodup
      source descriptor (0, 0))

/-- Exact retained-bend link quotient: global normalization and stable
deduplication remove precisely the nine translated copies and leave one
untranslated block per numeric route. -/
theorem drawingRouteBendLinks_wrappedNormalized_dedup_eq_base
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((drawingRouteBendLinks source.incidenceGraph).map
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization source))).dedup =
      baseBendNormalizedLinks source := by
  rw [drawingRouteBendLinks_wrappedNormalized_eq_neighborBlocks]
  have pairwiseIndices :
      (numericRouteDescriptors source).Pairwise
        (fun first second =>
          first.edgeIndex ≠ second.edgeIndex) := by
    rw [← List.pairwise_map]
    exact List.nodup_iff_pairwise_ne.mp
      (numericRouteDescriptor_edgeIndices_nodup source)
  have blocksDisjoint :
      (numericRouteDescriptors source).Pairwise
        (fun first second => List.Disjoint
          (neighborTranslations.flatMap fun translate =>
            translatedRouteBendNormalizedLinks
              source first translate)
          (neighborTranslations.flatMap fun translate =>
            translatedRouteBendNormalizedLinks
              source second translate)) :=
    pairwiseIndices.imp fun {first second} edgeIndexNe =>
      neighborRouteBendNormalizedLinks_disjoint_of_edgeIndex_ne
        source first second edgeIndexNe
  rw [List.dedup_flatMap_pairwise_disjoint
    (numericRouteDescriptors source)
    (fun descriptor => neighborTranslations.flatMap fun translate =>
      translatedRouteBendNormalizedLinks source descriptor translate)
    blocksDisjoint]
  unfold baseBendNormalizedLinks
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  exact neighborRouteBendNormalizedLinks_dedup_eq_base
    source descriptor

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

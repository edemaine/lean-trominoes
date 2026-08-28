/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordSelection
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendNumericSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics

/-! # Numeric-route semantics of affine compact bend atom words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- On the diagonal pair of a listed numeric route, the compact affine scan
is exactly the four-word occurrence block of every untranslated bend. -/
theorem bendCompactAtomWords_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (shape : RouteShape)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula)
    (shapeMatches : shape.Matches descriptor) :
    bendCompactAtomWords
        (RouteDescriptorPairFieldTags.descriptorPairTokens
          (descriptor, descriptor)) =
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        RouteBend.compactAtomWords := by
  rw [bendCompactAtomWords_eq_of_matches shape
    (descriptor, descriptor) rfl shapeMatches]
  · rw [← shape.map_evalPair_baseBendTemplates
      (descriptor, descriptor) shapeMatches,
      List.flatMap_map]
  · intro template templateMember
    exact (shape.baseBendTemplate_directionsGenuine
      formula wellFormed degree isLocal descriptor descriptorMember
      shapeMatches templateMember).1
  · intro template templateMember
    exact (shape.baseBendTemplate_directionsGenuine
      formula wellFormed degree isLocal descriptor descriptorMember
      shapeMatches templateMember).2

/-- Pair-major compact bend words before delimiter encoding. -/
def affineBaseBendCompactAtomWordStream
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    bendCompactAtomWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)

/-- On numeric source-route descriptors, the pair-major selector emits
exactly every untranslated bend's four compact occurrence words, in semantic
route and bend order. -/
theorem affineBaseBendCompactAtomWordStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBaseBendCompactAtomWordStream
        ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
          (PeriodicCNF.numericRouteDescriptors formula)) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          RouteBend.compactAtomWords := by
  unfold affineBaseBendCompactAtomWordStream
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair => bendCompactAtomWords
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
        formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact bendCompactAtomWords_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact bendCompactAtomWords_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

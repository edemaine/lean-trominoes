/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionSelection
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendNumericSemantics

/-! # Numeric semantics of retained-bend route source-prefix selection -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

/-- On a listed numeric route's diagonal pair, the affine selector emits
exactly four source-prefix words for every semantic untranslated bend. -/
theorem affineBaseBendRoutePrefixDirectionBlock_numeric_diagonal
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
    affineBaseBendRoutePrefixDirectionBlock
        (descriptorPairTokens (descriptor, descriptor)) =
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          canonicalBendRoutePrefixDirectionBlock
            routeBend.incomingPort routeBend.outgoingPort := by
  rw [affineBaseBendRoutePrefixDirectionBlock_eq_of_matches
    shape (descriptor, descriptor) rfl shapeMatches]
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

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

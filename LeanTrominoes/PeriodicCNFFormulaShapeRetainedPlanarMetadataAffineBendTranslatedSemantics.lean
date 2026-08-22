/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendNumericSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendTranslationInvariance

/-! # Neighbor-translation semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Repeating the verified base scan over the nine neighboring translations
is exactly the complete translated bend enumeration of one numeric route. -/
theorem affineBendDescriptorBlock_numeric_diagonal
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
    affineBendDescriptorBlock
        (descriptorPairTokens (descriptor, descriptor)) =
      (neighborTranslations.flatMap fun translate =>
        routeBends descriptor.edgeIndex translate descriptor.route).flatMap
          fun routeBend =>
            canonicalBendDescriptorBlock
              routeBend.incomingPort routeBend.outgoingPort false := by
  unfold affineBendDescriptorBlock repeatNeighborBendDescriptorBlock
  rw [affineBaseBendDescriptorBlock_numeric_diagonal
    formula wellFormed degree isLocal shape descriptor
    descriptorMember shapeMatches]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro translate _translateMember
  exact (routeBends_descriptorBlocks_translate
    descriptor.edgeIndex translate (0, 0) descriptor.route).symm

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionNumericSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionOffDiagonalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics

/-! # Stream semantics of complete retained-bend route words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags

@[simp] theorem affineBaseBendRouteDirectionStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    affineBaseBendRouteDirectionStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        affineBaseBendRouteDirectionBlock (descriptorPairTokens pair) := by
  unfold affineBaseBendRouteDirectionStream
  rw [mappedOutput_encodeDescriptorPairs]

/-- On numeric source-route descriptors, the compiled pair-major selector
emits exactly the complete delimited word block of every untranslated bend,
in semantic route and bend order. -/
theorem affineBaseBendRouteDirectionStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBaseBendRouteDirectionStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            canonicalBendRouteDirectionBlock
              routeBend.incomingPort routeBend.outgoingPort := by
  rw [affineBaseBendRouteDirectionStream_encodeDescriptorPairs]
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair =>
      affineBaseBendRouteDirectionBlock (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
        formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact affineBaseBendRouteDirectionBlock_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact affineBaseBendRouteDirectionBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

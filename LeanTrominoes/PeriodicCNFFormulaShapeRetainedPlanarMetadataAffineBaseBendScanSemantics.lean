/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBaseBendScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendNumericSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendOffDiagonalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics

/-! # Semantics of untranslated retained-bend descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

@[simp] theorem affineBaseBendDescriptorStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    affineBaseBendDescriptorStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        affineBaseBendDescriptorBlock (descriptorPairTokens pair) := by
  unfold affineBaseBendDescriptorStream
  rw [mappedOutput_encodeDescriptorPairs]

/-- On numeric route descriptors the base scan emits exactly one canonical
block for each untranslated bend. -/
theorem affineBaseBendDescriptorStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBaseBendDescriptorStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            canonicalBendDescriptorBlock
              routeBend.incomingPort routeBend.outgoingPort false := by
  rw [affineBaseBendDescriptorStream_encodeDescriptorPairs]
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair =>
      affineBaseBendDescriptorBlock (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact affineBaseBendDescriptorBlock_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact affineBaseBendDescriptorBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

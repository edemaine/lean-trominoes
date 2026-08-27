/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordNumericSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordOffDiagonalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics

/-! # Stream semantics of retained-bend Figure 9 records -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

@[simp] theorem affineBaseBendRouteTailRecordStream_encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    affineBaseBendRouteTailRecordStream (encodeDescriptorPairs pairs) =
      pairs.flatMap fun pair =>
        affineBaseBendRouteTailRecordBlock
          (descriptorPairTokens pair) := by
  unfold affineBaseBendRouteTailRecordStream
  rw [mappedOutput_encodeDescriptorPairs]

/-- On numeric source routes, the pair-major selector emits exactly one
canonical Figure 9 record block for every untranslated retained bend. -/
theorem affineBaseBendRouteTailRecordStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBaseBendRouteTailRecordStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
          fun routeBend =>
            bendRouteTailRecordBlock
              routeBend.incomingPort routeBend.outgoingPort false := by
  rw [affineBaseBendRouteTailRecordStream_encodeDescriptorPairs]
  rw [numericRouteDescriptorSquare_flatMap_eq_diagonal
    formula
    (fun pair =>
      affineBaseBendRouteTailRecordBlock (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
        formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact affineBaseBendRouteTailRecordBlock_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first firstMember second secondMember edgeIndexNe
    exact affineBaseBendRouteTailRecordBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

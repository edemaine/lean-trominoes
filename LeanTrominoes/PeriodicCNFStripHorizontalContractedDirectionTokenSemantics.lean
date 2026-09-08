/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalContractedDirectionBlockListData

/-! # Canonical contracted blocks emit the geometric route-word stream -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicThreeDM

/-- Assembling correct incidence blocks emits exactly one delimited geometric
route word per canonical contracted edge, in the same edge order. -/
theorem horizontalContractedDirectionBlocks_outputTokens
    (source : PeriodicCNF Nat)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (correct : HorizontalIncidenceDirectionBlocksCorrect source incidenceBlock) :
    ContractedDirectionAssembler.outputTokens
        ((horizontalContractedDirectionBlocks
          (horizontalThreeDMProblemComputed source) incidenceBlock).map fun tagged =>
            HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge tagged.2) =
      (horizontalThreeDMProblemComputed source).contractedEdges.flatMap (fun edge =>
        NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
          (horizontalAssembledContractedDirections source edge)) := by
  calc
    _ = (horizontalContractedDirectionBlocks
        (horizontalThreeDMProblemComputed source) incidenceBlock).flatMap (fun tagged =>
          NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
            (horizontalAssembledContractedDirections source tagged.1)) := by
      unfold ContractedDirectionAssembler.outputTokens
      rw [List.flatMap_map]
      apply List.flatMap_congr
      intro tagged member
      rw [HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge_directions,
        horizontalContractedDirectionBlocks_directions source incidenceBlock correct tagged member]
    _ = _ := by
      simpa only [List.flatMap_map] using congrArg
        (fun edges : List ContractedEdge => edges.flatMap (fun edge =>
          NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
            (horizontalAssembledContractedDirections source edge)))
        (map_fst_horizontalContractedDirectionBlocks
          (horizontalThreeDMProblemComputed source) incidenceBlock)

end LeanTrominoes.PeriodicCNFStripReduction

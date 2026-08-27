/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseValidRouteRequestData

/-! # Semantics of cursor-valid direct sparse route-request batches -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNFStripReduction.RouteRasterRequest
open GadgetSparseRouteRecordMachine

/-- The batch machine's physical input depends only on the underlying compact
requests, not on their cursor-validity proofs. -/
theorem routeRecordBatch_input_eq_normalizedTokens_map_val
    (requests : List ValidRequest) :
    GadgetSparseRouteRecordBatch.input requests =
      GadgetSparseRouteRasterNormalizedTokens.normalizedTokens
        (requests.map Subtype.val) := by
  unfold GadgetSparseRouteRecordBatch.input
    GadgetSparseRouteRasterNormalizedTokens.normalizedTokens
    validRequestInput
  rw [List.flatMap_map]

/-- Likewise, the batch output is the concatenation of the underlying
requests' complement-counter record blocks. -/
theorem routeRecordBatch_output_eq_complementBlocks_map_val
    (requests : List ValidRequest) :
    GadgetSparseRouteRecordBatch.output requests =
      (requests.map Subtype.val).flatMap complementRecordBlock := by
  unfold GadgetSparseRouteRecordBatch.output validRequestOutput
  rw [List.flatMap_map]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseValidRouteRequestSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The packaged direct batch is encoded by exactly the normalized unary
request stream produced by the raster-request normalizer. -/
theorem directSparseValidRouteRecordBatchInput_eq
    (symbols : List encoding.Γ) :
    GadgetSparseRouteRecordBatch.input
        (directSparseValidRouteRasterRequestsOfSymbols decider symbols) =
      GadgetSparseRouteRasterNormalizedTokens.normalizedTokens
        (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
          decider symbols) := by
  rw [routeRecordBatch_input_eq_normalizedTokens_map_val,
    directSparseValidRouteRasterRequests_map_val]

/-- The concrete complement-counter batch emits exactly the established
direct raster-direction route-record suffix. -/
theorem directSparseValidRouteRecordBatchOutput_eq
    (symbols : List encoding.Γ) :
    GadgetSparseRouteRecordBatch.output
        (directSparseValidRouteRasterRequestsOfSymbols decider symbols) =
      directSparseComputedRouteRasterDirectionRecordsOfSymbols
        decider symbols := by
  rw [routeRecordBatch_output_eq_complementBlocks_map_val,
    directSparseValidRouteRasterRequests_map_val]
  exact RouteRasterRequest.directSparseRouteComplementRequestBlocks_eq
    decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end

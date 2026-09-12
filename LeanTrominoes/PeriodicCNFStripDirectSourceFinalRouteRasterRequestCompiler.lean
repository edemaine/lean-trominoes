/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterRequestAssemblyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRasterVerticalCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRasterColorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteDirectionRequestCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRecordCompiler

/-! # Unconditional compiler for the actual direct sparse raster request stream -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicThreeDM.NormalizationDirectionRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Raster and normalization requests enumerate the same actual contracted edges. -/
theorem directSparseRasterRequests_normalization_eq (symbols : List encoding.Γ) :
    (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.normalization) =
      directSparseRouteDirectionRequestsOfSymbols decider symbols := by
  unfold RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
    directSparseRouteDirectionRequestsOfSymbols
  rw [List.map_map]
  apply List.map_congr_left
  intro edge _
  rfl

private noncomputable def rasterNormalizationCompiler :
    @TM2ComputableInPolyTime (List encoding.Γ) (List Batch.Token) encoding.Γ Batch.Token id id
      (fun symbols => Batch.tokens
        ((RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
          (fun request => request.normalization))) := by
  have equal : (fun symbols => Batch.tokens
        ((RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
          (fun request => request.normalization))) =
      directSparseRouteDirectionRequestTokensOfSymbols decider := by
    funext symbols
    rw [directSparseRasterRequests_normalization_eq]
    rfl
  rw [equal]
  exact directSparseRouteDirectionRequestTokenCompiler decider

/-- The source-specific raster boundary is now an actual native machine:
all metadata, normalization headers, directions, and record ordering are compiled. -/
noncomputable def directSparseRouteRasterRequestTokenCompiler :
    DirectSparseRouteRasterRequestTokenCompiler decider := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    exact GadgetSparseRouteRasterRequestTokens.RequestAssembly.computableInPolyTimeOf
      id (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider)
      (directSourceFinalRasterGridFieldsComputableInPolyTime decider)
      (directSourceFinalRasterHorizontalCoordinatesComputableInPolyTime decider)
      (directSourceFinalRasterVerticalFieldsComputableInPolyTime decider)
      (directSourceFinalRasterColorFieldsComputableInPolyTime decider)
      (rasterNormalizationCompiler decider)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- The complete canonical route-record suffix is compiled without a source-emitter premise. -/
noncomputable def directSparseCanonicalRouteRecordCompiler :
    DirectSparseCanonicalRouteRecordCompiler decider :=
  directSparseCanonicalRouteRecordsComputableInPolyTimeOfRasterRequests decider
    (directSparseRouteRasterRequestTokenCompiler decider)

/-- The actual route appender required by the final split-appender closure. -/
noncomputable def directSparseRouteRecordAppender :
    DirectSparseRouteRecordAppender decider :=
  directSparseRouteRecordAppenderOfRasterRequests decider
    (directSparseRouteRasterRequestTokenCompiler decider)

end LeanTrominoes.PeriodicCNFStripReduction
end

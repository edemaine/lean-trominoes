/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseRouteRecordBatchCompiler
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseRouteRasterNormalizedTokenBatchCompiler
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseRouteRasterRequestTokenCompiler
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Render any compiled cursor-valid compact route request list -/
noncomputable section
namespace LeanTrominoes.GadgetSparseRouteRequestRenderingCompiler
open _root_.Computability Turing PeriodicCNFStripReduction.RouteRasterRequest
open GadgetSparseRouteRecordMachine (ValidRequest validRequestInput validRequestOutput)

private def certified (requests : List Request)
    (valid : ∀ request∈requests,request.metadata.CursorValid) : List ValidRequest :=
  requests.attach.map (fun request => ⟨request.1,valid request.1 request.2⟩)

private theorem certified_values (requests : List Request)
    (valid : ∀ request∈requests,request.metadata.CursorValid) :
    (certified requests valid).map Subtype.val=requests := by
  simp only [certified,List.map_map,Function.comp_def]
  exact List.attach_map_subtype_val requests

private theorem certified_input (requests : List Request)
    (valid : ∀ request∈requests,request.metadata.CursorValid) :
    GadgetSparseRouteRecordBatch.input (certified requests valid)=
      GadgetSparseRouteRasterNormalizedTokens.normalizedTokens requests := by
  have eq : GadgetSparseRouteRecordBatch.input (certified requests valid)=
      GadgetSparseRouteRasterNormalizedTokens.normalizedTokens
        ((certified requests valid).map Subtype.val) := by
    unfold GadgetSparseRouteRecordBatch.input GadgetSparseRouteRasterNormalizedTokens.normalizedTokens
      validRequestInput
    rw [List.flatMap_map]
  rw [eq,certified_values]

private theorem certified_output (requests : List Request)
    (valid : ∀ request∈requests,request.metadata.CursorValid) :
    GadgetSparseRouteRecordBatch.output (certified requests valid)=
      requests.flatMap normalizedRecordBlock := by
  have eq : GadgetSparseRouteRecordBatch.output (certified requests valid)=
      ((certified requests valid).map Subtype.val).flatMap complementRecordBlock := by
    unfold GadgetSparseRouteRecordBatch.output validRequestOutput
    rw [List.flatMap_map]
  rw [eq,certified_values]
  apply List.flatMap_congr
  intro request member
  exact complementRecordBlock_eq_normalizedRecordBlock request (valid request member)

/-- Affine expansion, three-round normalization, and the complement-counter
batch machine compose without any source-specific assumptions beyond validity. -/
def computableInPolyTime {Source Symbol : Type} [Fintype Symbol]
    (encodeSource : Source → List Symbol) (requests : Source → List Request)
    (emitter : TM2ComputableInPolyTime encodeSource id
      (fun source => GadgetSparseRouteRasterRequestTokens.tokens (requests source)))
    (valid : ∀ source request,request∈requests source → request.metadata.CursorValid) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => (requests source).flatMap normalizedRecordBlock) := by
  let expanded := TM2CompositionMachine.computableInPolyTime emitter
    GadgetSparseRouteRasterRequestTokens.computableInPolyTime
  let expandedExact : TM2ComputableInPolyTime encodeSource id
      (fun source => GadgetSparseRouteRasterRequestTokens.expandedTokens (requests source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq expanded
    (fun source => GadgetSparseRouteRasterRequestTokens.expand_tokens (requests source))
  let normalized := TM2CompositionMachine.computableInPolyTime expandedExact
    GadgetSparseRouteRasterNormalizedTokens.Batch.normalizedOutputComputableInPolyTime
  let ready : TM2ComputableInPolyTime encodeSource GadgetSparseRouteRecordBatch.input
      (fun source => certified (requests source) (valid source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq normalized
    (fun source => (GadgetSparseRouteRasterNormalizedTokens.Batch.normalizedOutput_expandedTokens
      (requests source)).trans (certified_input (requests source) (valid source)).symm)
  let rendered := TM2CompositionMachine.computableInPolyTime ready
    GadgetSparseRouteRecordBatch.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq rendered
    (fun source => certified_output (requests source) (valid source))
end LeanTrominoes.GadgetSparseRouteRequestRenderingCompiler

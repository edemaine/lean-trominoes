/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.GadgetSparseRouteRasterRequestTokens
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatch
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Serialize raster metadata and normalization requests in the same edge order -/

noncomputable section
namespace LeanTrominoes.GadgetSparseRouteRasterRequestTokens.RequestAssembly
open Computability Turing
open PeriodicCNFStripReduction.RouteRasterRequest

abbrev PackedToken := FiniteAlphabetDelimitedBlockJoin.Token Token
abbrev NormalizationBatchToken := PeriodicThreeDM.NormalizationDirectionRequest.Batch.Token

private def unaryBlock (suffix : List Token) : UnaryFieldEncoderMachine.Symbol → List PackedToken
  | .unit => [.value .scaledUnit]
  | .delimiter => suffix.map .value ++ [.blockEnd]

private theorem unaryBlock_field (suffix : List Token) (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap (unaryBlock suffix) =
      FiniteAlphabetDelimitedBlockJoin.block (List.replicate value .scaledUnit ++ suffix) := by
  induction value with
  | zero => simp [UnaryFieldEncoderMachine.unaryField, unaryBlock, FiniteAlphabetDelimitedBlockJoin.block]
  | succ value induction =>
      simpa only [UnaryFieldEncoderMachine.unaryField, List.replicate_succ,
        List.cons_append, List.flatMap_cons, unaryBlock, List.singleton_append, List.nil_append,
        FiniteAlphabetDelimitedBlockJoin.block, List.map_cons] using
        congrArg (List.cons (.value .scaledUnit)) induction

private theorem unaryBlock_fields (suffix : List Token) (values : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields values).flatMap (unaryBlock suffix) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (values.map (fun value => List.replicate value .scaledUnit ++ suffix)) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        unaryBlock_field, induction]
      rfl

private noncomputable def unaryBlocksComputableInPolyTime (suffix : List Token) :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id
      (fun values => FiniteAlphabetDelimitedBlockJoin.blocks
        (values.map (fun value => List.replicate value .scaledUnit ++ suffix))) :=
  TM2PolyTimeInputEncodingTransport.of_prepare UnaryFieldEncoderMachine.unaryFields
    (FiniteBlockTransducer.computableInPolyTime (unaryBlock suffix))
    (fun _ => rfl) (unaryBlock_fields suffix)

private def normalizationBlock : NormalizationBatchToken → List PackedToken
  | .request token => [.value (.normalization token)]
  | .requestEnd => [.blockEnd]

private theorem normalizationBlock_requests
    (requests : List PeriodicThreeDM.NormalizationDirectionRequest.Request) :
    (PeriodicThreeDM.NormalizationDirectionRequest.Batch.tokens requests).flatMap normalizationBlock =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (requests.map (fun request => request.tokens.map Token.normalization)) := by
  simp only [PeriodicThreeDM.NormalizationDirectionRequest.Batch.tokens,
    PeriodicThreeDM.NormalizationDirectionRequest.Batch.requestBlock,
    List.flatMap_assoc, List.flatMap_append, List.flatMap_map,
    normalizationBlock, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map,
    FiniteAlphabetDelimitedBlockJoin.block, List.map_map, Function.comp_def]
  simp only [← List.map_eq_flatMap]

private def finishBlock : PackedToken → List Token
  | .value token => [token]
  | .blockEnd => [.requestEnd]

private theorem finishBlock_blocks (bodies : List (List Token)) :
    (FiniteAlphabetDelimitedBlockJoin.blocks bodies).flatMap finishBlock =
      bodies.flatMap (fun body => body ++ [.requestEnd]) := by
  simp only [FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_assoc,
    FiniteAlphabetDelimitedBlockJoin.block, List.flatMap_append, List.flatMap_map,
    finishBlock, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp

private noncomputable def joinedFieldsComputableInPolyTime
    {Source SourceSymbol : Type} [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol) (requests : Source → List Request)
    (first second : Request → List Token)
    (firstCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks ((requests source).map first)))
    (secondCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks ((requests source).map second))) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks
        ((requests source).map (fun request => first request ++ second request))) := by
  let joined := FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf
    encodeSource _ _ firstCompiler secondCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq joined (fun source => by
    simpa only [List.map_map, Function.comp_def, id_eq] using
      FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
        ((requests source).map (fun request => (first request, second request))))

/-- Three unary metadata columns, one finite color column, and the existing
normalization batch suffice to serialize complete compact raster requests. -/
noncomputable def computableInPolyTimeOf
    {Source SourceSymbol : Type} [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol) (requests : Source → List Request)
    (gridCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => (requests source).map (fun request => request.metadata.gridSize)))
    (horizontalCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => (requests source).map (fun request => request.metadata.horizontal)))
    (verticalCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => (requests source).map (fun request => request.metadata.verticalComplement)))
    (colorCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => (requests source).map (fun request => request.metadata.color)))
    (normalizationCompiler : TM2ComputableInPolyTime encodeSource id
      (fun source => PeriodicThreeDM.NormalizationDirectionRequest.Batch.tokens
        ((requests source).map (fun request => request.normalization)))) :
    TM2ComputableInPolyTime encodeSource id (fun source => tokens (requests source)) := by
  let grid := TM2CompositionMachine.computableInPolyTime gridCompiler
    (unaryBlocksComputableInPolyTime [.periodEnd])
  let horizontal := TM2CompositionMachine.computableInPolyTime horizontalCompiler
    (unaryBlocksComputableInPolyTime [.horizontalOffset, .horizontalEnd])
  let vertical := TM2CompositionMachine.computableInPolyTime verticalCompiler
    (unaryBlocksComputableInPolyTime [.verticalOffset, .verticalEnd])
  let colors := TM2CompositionMachine.computableInPolyTime colorCompiler
    (FiniteBlockTransducer.computableInPolyTime (fun color : Gadget.WireColor =>
      FiniteAlphabetDelimitedBlockJoin.block [Token.color color]))
  let normalization := TM2CompositionMachine.computableInPolyTime normalizationCompiler
    (FiniteBlockTransducer.computableInPolyTime normalizationBlock)
  let normalized : TM2ComputableInPolyTime encodeSource id
      (fun source => FiniteAlphabetDelimitedBlockJoin.blocks
        ((requests source).map (fun request => request.normalization.tokens.map Token.normalization))) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq normalization (fun source => by
      rw [normalizationBlock_requests, List.map_map]
      rfl)
  let gridHorizontal := joinedFieldsComputableInPolyTime encodeSource requests _ _
    (by simpa only [List.map_map, Function.comp_def] using grid)
    (by simpa only [List.map_map, Function.comp_def] using horizontal)
  let coordinates := joinedFieldsComputableInPolyTime encodeSource requests _ _ gridHorizontal
    (by simpa only [List.map_map, Function.comp_def] using vertical)
  let metadata := joinedFieldsComputableInPolyTime encodeSource requests _ _ coordinates
    (by simpa only [FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map] using colors)
  let complete := joinedFieldsComputableInPolyTime encodeSource requests _ _ metadata normalized
  let finished := TM2CompositionMachine.computableInPolyTime complete
    (FiniteBlockTransducer.computableInPolyTime finishBlock)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq finished (fun source => by
    rw [finishBlock_blocks, List.flatMap_map]
    change _ = (requests source).flatMap requestBlock
    apply List.flatMap_congr
    intro request _
    simp [requestBlock, requestTokens, metadataTokens, List.append_assoc])

end LeanTrominoes.GadgetSparseRouteRasterRequestTokens.RequestAssembly
end

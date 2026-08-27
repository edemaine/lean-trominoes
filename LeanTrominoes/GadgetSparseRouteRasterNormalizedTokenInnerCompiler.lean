/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenFinalizer
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenSemantics
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestThreeRoundCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Inner compiler for one expanded raster route request -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseRouteRasterNormalizedTokens

open Computability Turing
open GadgetSparseRouteRasterRequestTokens
open PeriodicCNFStripReduction.RouteRasterRequest

noncomputable def metadataOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id metadataOutput := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List ExpandedToken => tokens.flatMap metadataBlock)
  exact FiniteBlockTransducer.computableInPolyTime metadataBlock

noncomputable def normalizationInputComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizationInput := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List ExpandedToken => tokens.flatMap normalizationBlock)
  exact FiniteBlockTransducer.computableInPolyTime normalizationBlock

/-- Physical normalized-direction suffix for one expanded block. -/
def normalizedDirectionOutput (tokens : List ExpandedToken) : List Token :=
  DirectionFinalizer.output
    (PeriodicThreeDM.NormalizationDirectionRequest.threeRoundDirectionsOutput
      (normalizationInput tokens))

noncomputable def normalizedDirectionOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedDirectionOutput := by
  let extracted := normalizationInputComputableInPolyTime
  let normalized := TM2CompositionMachine.computableInPolyTime extracted
    PeriodicThreeDM.NormalizationDirectionRequest.threeRoundDirectionsOutputComputableInPolyTime
  let finalized := TM2CompositionMachine.computableInPolyTime normalized
    DirectionFinalizer.computableInPolyTime
  exact finalized

/-- Drop the fork separator and concatenate its two token streams. -/
def separatedBlock :
    SeparatedProductEncoding.Token Token Token → List Token
  | .left token => [token]
  | .separator => []
  | .right token => [token]

def separatedFlatten
    (tokens : List (SeparatedProductEncoding.Token Token Token)) :
    List Token :=
  tokens.flatMap separatedBlock

@[simp] theorem separatedFlatten_encode
    (first second : List Token) :
    separatedFlatten
        (SeparatedProductEncoding.encode id id (first, second)) =
      first ++ second := by
  simp [separatedFlatten, separatedBlock,
    SeparatedProductEncoding.encode, List.flatMap_map]

noncomputable def separatedFlattenComputableInPolyTime :
    TM2ComputableInPolyTime id id separatedFlatten := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List (SeparatedProductEncoding.Token Token Token) =>
      tokens.flatMap separatedBlock)
  exact FiniteBlockTransducer.computableInPolyTime separatedBlock

/-- Pair concatenation compiled through its separated tape encoding. -/
noncomputable def pairFlattenComputableInPolyTime :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode id id) id
      (fun pair : List Token × List Token => pair.1 ++ pair.2) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode id id)
    separatedFlattenComputableInPolyTime
    (fun _ => rfl)
    (fun pair => by
      rcases pair with ⟨first, second⟩
      exact separatedFlatten_encode first second)

/-- Mathematical output of the complete one-request inner pipeline. -/
def innerOutput (tokens : List ExpandedToken) : List Token :=
  metadataOutput tokens ++
    directionOutput
      (PeriodicThreeDM.NormalizationDirectionRequest.threeRoundDirectionsOutput
        (normalizationInput tokens))

/-- Metadata projection, dynamic three-round normalization, and finalization
form one polynomial-time block compiler. -/
noncomputable def innerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id innerOutput := by
  let forked := TM2ForkMachine.computableInPolyTime
    metadataOutputComputableInPolyTime
    normalizedDirectionOutputComputableInPolyTime
  let flattened := TM2CompositionMachine.computableInPolyTime forked
    pairFlattenComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq flattened
    (fun tokens => by
      unfold innerOutput normalizedDirectionOutput
      rw [DirectionFinalizer.output_eq])

/-- On a canonical request block the physical inner pipeline returns its
canonical normalized unary metadata and direction block. -/
@[simp] theorem innerOutput_expandedRequestBlock (request : Request) :
    innerOutput (expandedRequestBlock request) =
      normalizedRequestBlock request := by
  unfold innerOutput normalizedRequestBlock
  rw [metadataOutput_expandedRequestBlock,
    normalizationInput_expandedRequestBlock]
  rw [PeriodicThreeDM.NormalizationDirectionRequest.threeRoundDirectionsOutput_request]

end GadgetSparseRouteRasterNormalizedTokens
end LeanTrominoes

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicThreeDMContractedRouteRasterSourceData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for framed contracted raster requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace ContractedRouteRasterSource

open Computability Turing

noncomputable def prefixTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id prefixTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap prefixBlock)
  exact FiniteBlockTransducer.computableInPolyTime prefixBlock

noncomputable def incidenceTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id incidenceTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap incidenceBlock)
  exact FiniteBlockTransducer.computableInPolyTime incidenceBlock

noncomputable def assembledDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id fun tokens : List Token =>
      ContractedDirectionAssembler.output (incidenceTokens tokens) :=
  TM2CompositionMachine.computableInPolyTime
    incidenceTokensComputableInPolyTime
    ContractedDirectionAssembler.outputComputableInPolyTime

noncomputable def separatedFlattenComputableInPolyTime :
    TM2ComputableInPolyTime id id separatedFlatten := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List
      (SeparatedProductEncoding.Token RasterToken
        NormalizationDirectionRequest.Batch.NormalizedToken) =>
      tokens.flatMap separatedBlock)
  exact FiniteBlockTransducer.computableInPolyTime separatedBlock

noncomputable def pairFlattenComputableInPolyTime :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode id id) id
      (fun pair : List RasterToken ×
          List NormalizationDirectionRequest.Batch.NormalizedToken =>
        pair.1 ++ rasterizeDirections pair.2) := by
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode id id)
    separatedFlattenComputableInPolyTime
    (fun _ => rfl)
    (fun pair => by
      rcases pair with ⟨leading, directions⟩
      exact separatedFlatten_encode leading directions)

/-- Prefix extraction, role-driven contracted assembly, and finite token
reinterpretation compile one outer request block in polynomial time. -/
noncomputable def requestOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id requestOutput := by
  let forked := TM2ForkMachine.computableInPolyTime
    prefixTokensComputableInPolyTime
    assembledDirectionsComputableInPolyTime
  let flattened := TM2CompositionMachine.computableInPolyTime forked
    pairFlattenComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq flattened
    (fun tokens => by rfl)

/-- Complete fixed compiler over every outer-delimited contracted request. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (TM2EndDelimitedBlockMap.mappedOutput isEnd requestOutput) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    requestOutputComputableInPolyTime isEnd

end ContractedRouteRasterSource
end PeriodicThreeDM
end LeanTrominoes

end

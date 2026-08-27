/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalContractedRouteRasterSourceData
import LeanTrominoes.PeriodicThreeDMContractedRouteRasterSourceCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for framed compact horizontal contracted raster sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalContractedRouteRasterSource

open Computability Turing
open PeriodicThreeDM

noncomputable def prefixTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id prefixTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap prefixBlock)
  exact FiniteBlockTransducer.computableInPolyTime prefixBlock

noncomputable def requestTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id requestTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap requestBlock)
  exact FiniteBlockTransducer.computableInPolyTime requestBlock

noncomputable def assembledDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id fun tokens : List Token =>
      HorizontalContractedRoutedRequest.contractedOutput
        (requestTokens tokens) :=
  TM2CompositionMachine.computableInPolyTime
    requestTokensComputableInPolyTime
    HorizontalContractedRoutedRequest.contractedOutputComputableInPolyTime

/-- Prefix extraction and compact contracted assembly reuse the generic
finite rasterizing concatenation bridge. -/
noncomputable def requestOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id requestOutput := by
  let forked := TM2ForkMachine.computableInPolyTime
    prefixTokensComputableInPolyTime
    assembledDirectionsComputableInPolyTime
  let flattened := TM2CompositionMachine.computableInPolyTime forked
    ContractedRouteRasterSource.pairFlattenComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq flattened
    (fun tokens => by rfl)

/-- Complete fixed compiler over all outer-delimited compact contracted
requests. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (TM2EndDelimitedBlockMap.mappedOutput isEnd requestOutput) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    requestOutputComputableInPolyTime isEnd

end HorizontalContractedRouteRasterSource
end PeriodicCNFStripReduction
end LeanTrominoes

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenBatchCompiler
import LeanTrominoes.GadgetSparseRouteRasterRequestTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseValidRouteRequestSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Direct compact raster-route request compiler boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNFStripReduction.RouteRasterRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteRasterRequestCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The sole source-specific route boundary: emit one compact raster request
block per contracted edge. -/
abbrev DirectSparseRouteRasterRequestTokenCompiler :=
  TM2ComputableInPolyTime id id fun symbols : List encoding.Γ =>
    GadgetSparseRouteRasterRequestTokens.tokens
      (directSparseRouteRasterRequestsOfSymbols decider symbols)

/-- Fixed three-pass affine expansion turns the compact stream into expanded
unary raster requests. -/
noncomputable def directSparseExpandedRouteRasterRequestTokensComputableInPolyTime
    (requests : DirectSparseRouteRasterRequestTokenCompiler decider) :
    TM2ComputableInPolyTime id id fun symbols : List encoding.Γ =>
      GadgetSparseRouteRasterRequestTokens.expandedTokens
        (directSparseRouteRasterRequestsOfSymbols decider symbols) := by
  let expanded := TM2CompositionMachine.computableInPolyTime requests
    GadgetSparseRouteRasterRequestTokens.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq expanded
    (fun symbols => by
      simpa only [id_eq] using
        GadgetSparseRouteRasterRequestTokens.expand_tokens
          (directSparseRouteRasterRequestsOfSymbols decider symbols))

/-- The block normalizer produces the exact canonical unary request stream. -/
noncomputable def directSparseNormalizedRouteRasterRequestTokensComputableInPolyTime
    (requests : DirectSparseRouteRasterRequestTokenCompiler decider) :
    TM2ComputableInPolyTime id id fun symbols : List encoding.Γ =>
      GadgetSparseRouteRasterNormalizedTokens.normalizedTokens
        (directSparseRouteRasterRequestsOfSymbols decider symbols) := by
  let expanded :=
    directSparseExpandedRouteRasterRequestTokensComputableInPolyTime
      decider requests
  let normalized := TM2CompositionMachine.computableInPolyTime expanded
    GadgetSparseRouteRasterNormalizedTokens.Batch.normalizedOutputComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq normalized
    (fun symbols => by
      simpa only [id_eq] using
        GadgetSparseRouteRasterNormalizedTokens.Batch.normalizedOutput_expandedTokens
          (directSparseRouteRasterRequestsOfSymbols decider symbols))

/-- Reinterpret the normalized stream as the certified semantic list expected
by the concrete complement-counter batch compiler. -/
noncomputable def directSparseValidRouteRasterRequestsComputableInPolyTime
    (requests : DirectSparseRouteRasterRequestTokenCompiler decider) :
    TM2ComputableInPolyTime id GadgetSparseRouteRecordBatch.input
      (directSparseValidRouteRasterRequestsOfSymbols decider) := by
  let normalized :=
    directSparseNormalizedRouteRasterRequestTokensComputableInPolyTime
      decider requests
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq normalized
    (fun symbols => by
      simpa only [id_eq] using
        (directSparseValidRouteRecordBatchInput_eq decider symbols).symm)

end PeriodicCNFStripReduction
end LeanTrominoes

end

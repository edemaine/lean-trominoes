/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenData
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenCompiler

/-! # Polynomial-time source-occurrence route tokenization -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

open Computability Turing

/-- Normalize the occurrence tokens parsed from one promised source. -/
def sourceTokens
    (source : SourceSplitRouteDescriptorTokens.Source) : List Token :=
  normalize (SourceOccurrenceTokens.parsedSource source)

/-- Offset normalization after flat-CNF parsing is polynomial time. -/
noncomputable def sourceTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source (List Token)
      PeriodicCNFFlatEncoding.Symbol Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode id sourceTokens := by
  let normalizer := FiniteStateTransducer.computableInPolyTime
    false transition finish
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceTokens.parsedSourceComputableInPolyTime normalizer
  change @TM2ComputableInPolyTime
    SourceSplitRouteDescriptorTokens.Source (List Token)
    PeriodicCNFFlatEncoding.Symbol Token
    SourceSplitRouteDescriptorTokens.finEncoding.encode id
    (fun source => FiniteStateTransducer.output false transition finish
      (SourceOccurrenceTokens.parsedSource source))
  exact composed

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

end

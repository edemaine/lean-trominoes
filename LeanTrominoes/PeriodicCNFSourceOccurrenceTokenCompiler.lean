/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenData
import LeanTrominoes.PeriodicCNFSourceSplitRouteDescriptorTokenData

/-! # Polynomial-time flat-CNF occurrence tokenization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

open Computability Turing

/-- Physical parser output on the flat word of one promised source. -/
def parsedSource
    (source : SourceSplitRouteDescriptorTokens.Source) : List Token :=
  parse (SourceSplitRouteDescriptorTokens.finEncoding.encode source)

/-- The finite-state grammar scan is polynomial time on promised flat source
encodings. -/
noncomputable def parsedSourceComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source (List Token)
      PeriodicCNFFlatEncoding.Symbol Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode id parsedSource := by
  let parser := FiniteStateTransducer.computableInPolyTime
    initial transition finish
  refine
    { tm := parser.tm
      inputAlphabet := parser.inputAlphabet
      outputAlphabet := parser.outputAlphabet
      time := parser.time
      outputsFun := ?_ }
  intro source
  unfold parsedSource parse
  exact parser.outputsFun
    (SourceSplitRouteDescriptorTokens.finEncoding.encode source)

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes

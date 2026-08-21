/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenFormulaSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Semantic polynomial-time occurrence tokenization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

open Computability Turing

/-- The physical promised-source parser is exactly the semantic occurrence
stream of its underlying formula. -/
theorem parsedSource_eq_formulaTokens
    (source : SourceSplitRouteDescriptorTokens.Source) :
    parsedSource source = formulaTokens source.formula := by
  unfold parsedSource
  rw [SourceSplitRouteDescriptorTokens.finEncoding_encode]
  exact parse_finEncoding_encode source.formula source.widthAtMostThree

/-- The semantic occurrence-token stream of a promised flat source is
computable in polynomial time. -/
noncomputable def formulaTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source (List Token)
      PeriodicCNFFlatEncoding.Symbol Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode id
      (fun source => formulaTokens source.formula) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    parsedSourceComputableInPolyTime fun source => by
      simpa using parsedSource_eq_formulaTokens source

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes

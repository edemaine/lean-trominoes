/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomLastContributionCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Polynomial-time starts of source last-occurrence contributions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomContributionStarts

open Turing

/-- Prefix sums immediately before each occurrence's possible retained group
size.  At a last occurrence, this is its atom block's starting index. -/
def starts (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  PrefixSums.starts
    (SourceOccurrenceAtomLastContributions.contributions source)

/-- Contribution-prefix starts are emitted as unary fields in polynomial
time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields starts := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomLastContributions.unaryFieldsComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime
  exact composed

end SourceOccurrenceAtomContributionStarts
end PeriodicCNF
end LeanTrominoes

end

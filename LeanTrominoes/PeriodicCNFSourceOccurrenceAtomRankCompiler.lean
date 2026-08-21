/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTime
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time source occurrence ranks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomRanks

open Computability Turing

/-- Stable within-atom rank of every source literal occurrence. -/
def ranks (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  DelimitedBinaryWordPrefixTrueCounts.counts
    (SourceOccurrenceAtomEqualityRows.rows source)

/-- Source occurrence ranks are emitted as unary natural fields in polynomial
time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields ranks := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomEqualityRows.rowsComputableInPolyTime
    DelimitedBinaryWordPrefixTrueCountMachine.computableInPolyTime
  exact composed

end SourceOccurrenceAtomRanks
end PeriodicCNF
end LeanTrominoes

end

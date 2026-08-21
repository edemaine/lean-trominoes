/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Source atom-group sizes in occurrence order -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomPerOccurrenceGroupSizes

open Turing

/-- The size of the atom group containing each source occurrence, listed in
source occurrence order. -/
def sizes (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (SourceOccurrenceAtomEqualityRows.rows source)

/-- Per-occurrence source atom-group sizes are emitted as unary fields in
polynomial time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields sizes := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomEqualityRows.rowsComputableInPolyTime
    DelimitedBinaryWordTrueCounts.computableInPolyTime
  exact composed

end SourceOccurrenceAtomPerOccurrenceGroupSizes
end PeriodicCNF
end LeanTrominoes

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRepresentativeRowCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time source atom-group sizes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomGroupSizes

open Computability Turing

/-- Occurrence count of every distinct source atom, in the last-occurrence
order used by `PeriodicThreeSATThree.sourceVariables`.  Each representative
equality row contributes its number of `true` entries. -/
def sizes (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (SourceOccurrenceAtomRepresentativeRows.rows source)

/-- Stable source atom-group sizes are emitted as unary natural fields in
polynomial time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields sizes := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomRepresentativeRows.rowsComputableInPolyTime
    DelimitedBinaryWordTrueCounts.computableInPolyTime
  exact composed

end SourceOccurrenceAtomGroupSizes
end PeriodicCNF
end LeanTrominoes

end

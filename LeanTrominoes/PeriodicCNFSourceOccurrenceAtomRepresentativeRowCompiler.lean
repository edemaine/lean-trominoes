/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowCompiler
import LeanTrominoes.LastRepresentativeEqualityRowsTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time last representatives of source atom classes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomRepresentativeRows

open Computability Turing

/-- Equality-matrix rows whose occurrences are the last members of their
atom-equality classes, matching Lean's `List.dedup` order. -/
def rows (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.rows
    (SourceOccurrenceAtomEqualityRows.rows source)

/-- Stable source atom representatives are computable in polynomial time. -/
noncomputable def rowsComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source DelimitedBinaryWords.Input
      PeriodicCNFFlatEncoding.Symbol DelimitedBinaryWords.Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode rows := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomEqualityRows.rowsComputableInPolyTime
    LastRepresentativeEqualityRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _ => rfl)

end SourceOccurrenceAtomRepresentativeRows
end PeriodicCNF
end LeanTrominoes

end

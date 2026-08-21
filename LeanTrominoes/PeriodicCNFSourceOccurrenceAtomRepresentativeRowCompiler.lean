/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowCompiler
import LeanTrominoes.RepresentativeEqualityRowsTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time stable representatives of source atom classes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomRepresentativeRows

open Computability Turing

/-- Equality-matrix rows whose occurrences are the first members of their
atom-equality classes, retained in stable occurrence order. -/
def rows (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWords.Input :=
  RepresentativeEqualityRows.rows
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
    RepresentativeEqualityRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _ => rfl)

end SourceOccurrenceAtomRepresentativeRows
end PeriodicCNF
end LeanTrominoes

end

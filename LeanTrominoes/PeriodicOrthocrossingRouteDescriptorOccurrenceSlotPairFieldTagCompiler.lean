/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTags
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Compiler for twelve-field descriptor occurrence-slot pair tags -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

open Computability Turing

/-- Tagging pair sides and modulo-twelve field positions is a fixed
finite-state transduction. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output Control.between transition finish)
  exact FiniteStateTransducer.computableInPolyTime
    Control.between transition finish

/-- The same tagger at the semantic delimiter-encoded word-pair boundary. -/
noncomputable def inputTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode id inputTokens :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWordPairs.finEncoding.encode
    tokensComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing

end

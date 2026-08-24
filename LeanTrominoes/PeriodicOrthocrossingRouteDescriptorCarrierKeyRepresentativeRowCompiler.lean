/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowData

/-! # Compiler interface for padded carrier-key representatives -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing
open PaddedSupportedCandidateWords

/-- A polynomial-time emitter for the complete guarded carrier-key word
stream composes with the generic representative pipeline to compute the
sentinel-free retained carrier-key rows. -/
noncomputable def paddedCarrierKeyRepresentativeRowsComputableInPolyTime
    {InputSymbol : Type}
    (encodeDescriptors : List RouteDescriptor → List InputSymbol)
    (wordCompiler :
      @TM2ComputableInPolyTime
        (List RouteDescriptor) DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token
        encodeDescriptors DelimitedBinaryWords.finEncoding.encode
        paddedCarrierKeyWordsWithSentinel) :
    @TM2ComputableInPolyTime
      (List RouteDescriptor) DelimitedBinaryWords.Input
      InputSymbol DelimitedBinaryWords.Token
      encodeDescriptors DelimitedBinaryWords.finEncoding.encode
      paddedCarrierKeyRepresentativeRows := by
  unfold paddedCarrierKeyRepresentativeRows
  change TM2ComputableInPolyTime encodeDescriptors
      DelimitedBinaryWords.finEncoding.encode
      (fun input => wordsWithSentinel CarrierKeyWords.word
        (paddedCarrierKeyCandidateStream input)) at wordCompiler
  exact representativeRowsComputableInPolyTime
    encodeDescriptors CarrierKeyWords.word
    paddedCarrierKeyCandidateStream wordCompiler

end LeanTrominoes.PeriodicOrthocrossing

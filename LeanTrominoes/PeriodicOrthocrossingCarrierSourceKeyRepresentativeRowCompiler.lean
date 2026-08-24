/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeySentinelCompiler

/-! # Compiler for compact carrier source-key representative rows -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing
open PaddedSupportedCandidateWords

noncomputable def paddedCarrierSourceKeyRepresentativeRowsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode
      paddedCarrierSourceKeyRepresentativeRows :=
  representativeRowsComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    CarrierNodeSourceKeys.word paddedCarrierSourceKeyCandidateStream
    paddedCarrierSourceKeyWordsWithSentinelComputableInPolyTime

end LeanTrominoes.PeriodicOrthocrossing

end

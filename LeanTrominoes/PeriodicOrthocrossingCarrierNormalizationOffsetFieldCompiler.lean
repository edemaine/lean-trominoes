/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetCandidateFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for carrier normalization-offset fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetField

open Computability Turing

noncomputable def valuesComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (CarrierNormalizationOffsetCandidateFieldStream.valuesWithSentinel field)
    (CarrierNormalizationOffsetCandidateFieldStream.valuesWithSentinel_length_sourceKeyCandidates
      field)
    (CarrierNormalizationOffsetCandidateFieldStream.valuesWithSentinelComputableInPolyTime
      field)

end CarrierNormalizationOffsetField
end LeanTrominoes.PeriodicOrthocrossing

end

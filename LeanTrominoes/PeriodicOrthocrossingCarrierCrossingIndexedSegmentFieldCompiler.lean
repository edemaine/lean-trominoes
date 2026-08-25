/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentCandidateFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for indexed crossing-segment fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingIndexedSegmentField

open Computability Turing

noncomputable def valuesComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (CarrierCrossingIndexedSegmentCandidateFieldStream.valuesWithSentinel field)
    (CarrierCrossingIndexedSegmentCandidateFieldStream.valuesWithSentinel_length_sourceKeyCandidates
      field)
    (CarrierCrossingIndexedSegmentCandidateFieldStream.valuesWithSentinelComputableInPolyTime
      field)

end CarrierCrossingIndexedSegmentField
end LeanTrominoes.PeriodicOrthocrossing

end

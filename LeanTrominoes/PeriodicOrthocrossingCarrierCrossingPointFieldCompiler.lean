/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for crossing-point fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointField

open Computability Turing

noncomputable def valuesComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (CarrierCrossingPointCandidateFieldStream.valuesWithSentinel field)
    (CarrierCrossingPointCandidateFieldStream.valuesWithSentinel_length_sourceKeyCandidates
      field)
    (CarrierCrossingPointCandidateFieldStream.valuesWithSentinelComputableInPolyTime
      field)

end CarrierCrossingPointField
end LeanTrominoes.PeriodicOrthocrossing

end

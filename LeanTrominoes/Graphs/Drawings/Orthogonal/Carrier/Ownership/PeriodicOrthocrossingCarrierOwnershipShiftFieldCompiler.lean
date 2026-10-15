/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Ownership.PeriodicOrthocrossingCarrierOwnershipShiftCandidateFieldLength
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Ownership.PeriodicOrthocrossingCarrierOwnershipShiftFieldLookupData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for carrier ownership-shift fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOwnershipShiftField

open Computability Turing

noncomputable def valuesComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (CarrierOwnershipShiftCandidateFieldStream.valuesWithSentinel field)
    (CarrierOwnershipShiftCandidateFieldStream.valuesWithSentinel_length_sourceKeyCandidates
      field)
    (CarrierOwnershipShiftCandidateFieldStream.valuesWithSentinelComputableInPolyTime
      field)

end CarrierOwnershipShiftField
end LeanTrominoes.PeriodicOrthocrossing

end

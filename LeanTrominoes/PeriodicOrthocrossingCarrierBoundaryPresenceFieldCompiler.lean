/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceAlignedCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for the selected carrier boundary-presence field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

open Computability Turing

noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields values :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    alignedValuesWithSentinel
    alignedValuesWithSentinel_length_sourceKeyCandidates
    alignedValuesWithSentinelComputableInPolyTime

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end

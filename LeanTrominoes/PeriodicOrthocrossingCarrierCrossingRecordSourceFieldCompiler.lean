/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldAlignedCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for selected source-key crossing-record fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

open Computability Turing

noncomputable def valuesComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (alignedValuesWithSentinel field)
    (alignedValuesWithSentinel_length_sourceKeyCandidates field)
    (alignedValuesWithSentinelComputableInPolyTime field)

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end

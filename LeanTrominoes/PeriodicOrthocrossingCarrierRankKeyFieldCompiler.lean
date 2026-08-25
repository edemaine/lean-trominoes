/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldAlignedCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupCompiler

/-! # Compiler for all selected carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyField

open Computability Turing

/-- Every semantically verified carrier-key column is emitted at all
deduplicated carrier-node representatives in polynomial time. -/
noncomputable def valuesComputableInPolyTime
    (field : CarrierKeyFieldProjector.Field)
    (wordCorrect : CarrierKeyFieldProjector.WordCorrect field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (values field) :=
  CarrierSourceKeyRepresentativeLookup.valuesComputableInPolyTime
    (alignedValuesWithSentinel field)
    (alignedValuesWithSentinel_length_sourceKeyCandidates field)
    (alignedValuesWithSentinelComputableInPolyTime field wordCorrect)

end CarrierRankKeyField
end LeanTrominoes.PeriodicOrthocrossing

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyMergedStreamData
import LeanTrominoes.TM2CompositionMachine

/-! # Complete merged carrier source-key stream compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyMergedStream

open Computability Turing

/-- Reinterpret the physical merger on canonical descriptor words without
adding another compiler-heavy wrapper module. -/
noncomputable def descriptorTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors =>
        tokens (RouteDescriptorBinaryWords.words descriptors)) := by
  change TM2ComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    id
    (fun descriptors => DelimitedBinaryWordGuardedPairMerge.tokens
      (CarrierSourceKeyComponentStream.tokens
        (RouteDescriptorBinaryWords.words descriptors)))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyComponentStream.descriptorTokensComputableInPolyTime
    DelimitedBinaryWordGuardedPairMerge.tokensComputableInPolyTime

end CarrierSourceKeyMergedStream
end LeanTrominoes.PeriodicOrthocrossing

end

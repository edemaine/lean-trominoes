/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyAllFieldStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyComponentStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for normalized padded carrier source-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyAllFieldStream

open Computability Turing

def emittedFields (descriptors : List RouteDescriptor) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierKeyAllFieldProjector.output
    (CarrierNormalizedSourceKeyComponentStream.tokens
      (RouteDescriptorBinaryWords.words descriptors))

noncomputable def emittedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id emittedFields := by
  change TM2ComputableInPolyTime
    (fun descriptors : List RouteDescriptor =>
      DelimitedBinaryWords.encode
        (RouteDescriptorBinaryWords.words descriptors))
    id
    (fun descriptors => CarrierKeyAllFieldProjector.output
      (CarrierNormalizedSourceKeyComponentStream.tokens
        (RouteDescriptorBinaryWords.words descriptors)))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierNormalizedSourceKeyComponentStream.descriptorTokensComputableInPolyTime
    CarrierKeyAllFieldProjector.computableInPolyTime

end CarrierNormalizedSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end

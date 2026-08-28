/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyAllFieldStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for all padded carrier-node source-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyAllFieldStream

open Computability Turing

/-- Physical twelve-field stream built from the established unmerged
source-key component emitter. -/
def emittedFields (descriptors : List RouteDescriptor) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierKeyAllFieldProjector.output
    (CarrierSourceKeyComponentStream.tokens
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
      (CarrierSourceKeyComponentStream.tokens
        (RouteDescriptorBinaryWords.words descriptors)))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierSourceKeyComponentStream.descriptorTokensComputableInPolyTime
    CarrierKeyAllFieldProjector.computableInPolyTime

end CarrierSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end

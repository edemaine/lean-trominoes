/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyAllFieldStreamData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyComponentStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for all shifted canonical crossing source-key pair fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyAllFieldStream

open Computability Turing

def emittedFields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierKeyAllFieldProjector.output
    (CanonicalCrossingShiftLeftSourceKeyComponentStream.emittedDescriptorStream
      input)

noncomputable def emittedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id emittedFields := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    (fun input => CarrierKeyAllFieldProjector.output
      (CanonicalCrossingShiftLeftSourceKeyComponentStream.emittedDescriptorStream
        input))
  exact TM2CompositionMachine.computableInPolyTime
    CanonicalCrossingShiftLeftSourceKeyComponentStream.emittedDescriptorStreamComputableInPolyTime
    CarrierKeyAllFieldProjector.computableInPolyTime

end CanonicalCrossingShiftLeftSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end

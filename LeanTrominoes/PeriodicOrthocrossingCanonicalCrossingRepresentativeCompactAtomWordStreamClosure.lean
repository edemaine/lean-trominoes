/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingRepresentativeCompactAtomWordStreamCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Postcomposition by canonical crossover compact-word expansion -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingRepresentativeCompactAtomWordStream

open Computability Turing

/-- Any polynomial-time producer of canonically encoded numeric route
descriptors composes with the representative crossover-word compiler. -/
opaque emittedTokensComputableInPolyTimeAfter
    {Input InputSymbol : Type}
    [Fintype InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (descriptors : Input → List RouteDescriptor)
    (compiler : @TM2ComputableInPolyTime
      Input (List RouteDescriptor) InputSymbol DelimitedBinaryWords.Token
      encodeInput descriptorInputEncoding descriptors) :
    @TM2ComputableInPolyTime
      Input (List DelimitedBinaryWords.Token)
      InputSymbol DelimitedBinaryWords.Token encodeInput id
      (fun input => emittedTokens (descriptors input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    emittedTokensComputableInPolyTime

/-- The same closure when the prepared descriptor compiler uses a
pointwise-equal spelling of the canonical descriptor encoding. -/
opaque emittedTokensComputableInPolyTimeAfterOfEncodingEq
    {Input InputSymbol : Type}
    [Fintype InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (encodeDescriptors :
      List RouteDescriptor → List DelimitedBinaryWords.Token)
    (descriptors : Input → List RouteDescriptor)
    (encodingEq : ∀ value,
      descriptorInputEncoding value = encodeDescriptors value)
    (compiler : @TM2ComputableInPolyTime
      Input (List RouteDescriptor) InputSymbol DelimitedBinaryWords.Token
      encodeInput encodeDescriptors descriptors) :
    @TM2ComputableInPolyTime
      Input (List DelimitedBinaryWords.Token)
      InputSymbol DelimitedBinaryWords.Token encodeInput id
      (fun input => emittedTokens (descriptors input)) := by
  let expanded : TM2ComputableInPolyTime encodeDescriptors id emittedTokens :=
    TM2PolyTimeInputEncodingTransport.of_prepare id
      emittedTokensComputableInPolyTime
      encodingEq (fun _ => rfl)
  exact TM2CompositionMachine.computableInPolyTime compiler expanded

end CanonicalCrossingRepresentativeCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing

end

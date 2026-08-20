/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPixelFiniteTokens
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time expansion of prepared gadget-pixel tokens -/

noncomputable section

namespace LeanTrominoes
namespace GadgetPixelFiniteTokenCompiler

open Computability Turing

/-- Compose any prepared-token emitter with the verified fixed affine block
expander and transport along its exact output equation. -/
def computableInPolyTimeOfEmitter
    {Input InputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {prepared : Input → List GadgetPixelFiniteTokens.Token}
    {tokens : Input → List PeriodicCNF.UnaryProgramTokens.Token}
    (emitter : TM2ComputableInPolyTime encodeInput id prepared)
    (correct : ∀ input,
      GadgetPixelFiniteTokens.expand (prepared input) = tokens input) :
    TM2ComputableInPolyTime encodeInput id tokens := by
  let expanded := TM2CompositionMachine.computableInPolyTime emitter
    GadgetPixelFiniteTokens.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq expanded
    correct

end GadgetPixelFiniteTokenCompiler
end LeanTrominoes


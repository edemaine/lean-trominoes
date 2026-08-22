/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity

/-! # Transporting polynomial-time machines across input encodings -/

noncomputable section

namespace LeanTrominoes.TM2PolyTimeInputEncodingTransport

open Computability Turing

/-- Reinterpret a polynomial-time machine on prepared semantic inputs when
the prepared and requested inputs have exactly the same finite encoding. -/
def of_prepare
    {Prepared Input Output InputSymbol OutputSymbol : Type}
    {encodePrepared : Prepared → List InputSymbol}
    {encodeInput : Input → List InputSymbol}
    {encodeOutput : Output → List OutputSymbol}
    {preparedFunction : Prepared → Output}
    {function : Input → Output}
    (prepare : Input → Prepared)
    (compiler :
      TM2ComputableInPolyTime encodePrepared encodeOutput preparedFunction)
    (encodedInputEq : ∀ input,
      encodePrepared (prepare input) = encodeInput input)
    (outputEq : ∀ input,
      preparedFunction (prepare input) = function input) :
    TM2ComputableInPolyTime encodeInput encodeOutput function where
  tm := compiler.tm
  inputAlphabet := compiler.inputAlphabet
  outputAlphabet := compiler.outputAlphabet
  time := compiler.time
  outputsFun input := by
    rw [← encodedInputEq input, ← outputEq input]
    exact compiler.outputsFun (prepare input)

end LeanTrominoes.TM2PolyTimeInputEncodingTransport

end

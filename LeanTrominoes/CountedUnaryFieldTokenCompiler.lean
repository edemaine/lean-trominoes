/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time postprocessing of counted unary field tokens -/

noncomputable section

namespace LeanTrominoes
namespace CountedUnaryFieldTokenCompiler

open Computability Turing
open PeriodicCNF.UnaryProgramTokens

/-- Count selected markers, expand finite unary tokens, and move that count
behind the next two fields. -/
def postprocess (tokens : List Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo
    (PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize tokens)

/-- The fixed counted-token postprocessor is polynomial-time. -/
noncomputable def postprocessComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List UnaryFieldEncoderMachine.Symbol)
      Token UnaryFieldEncoderMachine.Symbol id id postprocess := by
  let finalized :=
    PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalizeComputableInPolyTime
  let rotated := UnaryFieldHeaderRotationMachine.computableInPolyTime
  let composed := TM2CompositionMachine.computableInPolyTime finalized rotated
  change @TM2ComputableInPolyTime
    (List Token) (List UnaryFieldEncoderMachine.Symbol)
    Token UnaryFieldEncoderMachine.Symbol id id
    (fun tokens => UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo
      (PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize tokens))
  exact composed

/-- Compose an arbitrary polynomial-time counted-token emitter with the fixed
postprocessor and reinterpret its verified output as unary natural fields. -/
def computableInPolyTimeOfEmitter
    {Input InputSymbol : Type}
    {encodeInput : Input → List InputSymbol}
    {tokens : Input → List Token}
    {fields : Input → List Nat}
    (emitter : TM2ComputableInPolyTime encodeInput id tokens)
    (correct : ∀ input,
      postprocess (tokens input) =
        UnaryFieldEncoderMachine.unaryFields (fields input)) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fields := by
  let processed := TM2CompositionMachine.computableInPolyTime emitter
    postprocessComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq processed
    correct

end CountedUnaryFieldTokenCompiler
end LeanTrominoes

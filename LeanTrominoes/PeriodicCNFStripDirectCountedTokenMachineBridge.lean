/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectCountedTokenSemantics
import LeanTrominoes.CountedUnaryFieldTokenCompiler

/-! # Machine bridge from counted strip tokens to unary fields -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A polynomial-time counted-token emitter supplies the exact executable
unary-field emitter by composition with the two verified postprocessors. -/
def directCompiledTrominoStripPolyTimeOfCountedTokenEmitter
    (tromino : Tromino)
    (emitter :
      TM2ComputableInPolyTime id id
        (directCompiledTrominoStripCountedTokensOfSymbols
          decider tromino)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directExecutableTrominoStripFieldsOfSymbols decider tromino) := by
  exact CountedUnaryFieldTokenCompiler.computableInPolyTimeOfEmitter emitter
    (fun symbols =>
      rotate_countAndFinalize_directCompiledTrominoStripCountedTokens
        decider tromino symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

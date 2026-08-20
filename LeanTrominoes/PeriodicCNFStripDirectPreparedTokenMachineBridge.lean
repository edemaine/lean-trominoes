/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectPreparedTokenData
import LeanTrominoes.GadgetPixelFiniteTokenCompiler

/-! # Machine bridge from prepared geometric tokens to counted tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance preparedTokenMachineBridgeStackFintype
    (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A polynomial-time prepared-stream emitter composes with the fixed affine
expander to produce the required counted-token emitter. -/
def directCompiledTrominoStripCountedTokenEmitterOfPreparedEmitter
    (tromino : Tromino)
    (emitter :
      TM2ComputableInPolyTime id id
        (directCompiledTrominoStripPreparedTokensOfSymbols
          decider tromino)) :
    TM2ComputableInPolyTime id id
      (directCompiledTrominoStripCountedTokensOfSymbols
        decider tromino) := by
  exact GadgetPixelFiniteTokenCompiler.computableInPolyTimeOfEmitter emitter
    (fun symbols =>
      expand_directCompiledTrominoStripPreparedTokensOfSymbols
        decider tromino symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

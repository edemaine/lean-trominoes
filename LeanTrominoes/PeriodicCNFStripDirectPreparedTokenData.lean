/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetExpandedMotifFiniteTokens
import LeanTrominoes.PeriodicCNFStripDirectCountedTokens

/-! # Prepared finite-token data for direct strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance preparedTokenDataStackFintype
    (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Prepared finite stream for the proof-free normalized drawing and its
fixed gadget-pixel loop. -/
def directCompiledTrominoStripPreparedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    List GadgetPixelFiniteTokens.Token :=
  GadgetExpandedMotifFiniteTokens.preparedStripTokens tromino
    (directCompiledStripDrawingOfSymbols decider symbols)

/-- Fixed expansion of the prepared stream is the exact counted-token target
used by the established compiler bridge. -/
theorem expand_directCompiledTrominoStripPreparedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    GadgetPixelFiniteTokens.expand
        (directCompiledTrominoStripPreparedTokensOfSymbols
          decider tromino symbols) =
      directCompiledTrominoStripCountedTokensOfSymbols
        decider tromino symbols := by
  unfold directCompiledTrominoStripPreparedTokensOfSymbols
  rw [GadgetExpandedMotifFiniteTokens.expand_preparedStripTokens]
  unfold directCompiledTrominoStripCountedTokensOfSymbols
    directCompiledTrominoMotifOfSymbols
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

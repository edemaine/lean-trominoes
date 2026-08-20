/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectPreparedTokenMachineBridge
import LeanTrominoes.PeriodicCNFStripDirectCountedTokenCompiler

/-! # Prepared finite-token compiler interface for direct strip hardness -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

/-- Uniform prepared finite-token emitter contract for the remaining
normalization raster. -/
def DirectCompiledTrominoStripPreparedTokenEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id id
        (directCompiledTrominoStripPreparedTokensOfSymbols
          decider tromino))

theorem countedTokenEmitters_of_preparedTokenEmitters
    (emitters : DirectCompiledTrominoStripPreparedTokenEmitters) :
    DirectCompiledTrominoStripCountedTokenEmitters := by
  intro Input encoding language decider tromino
  exact (emitters encoding language decider tromino).map
    (directCompiledTrominoStripCountedTokenEmitterOfPreparedEmitter
      decider tromino)

/-- Prepared finite-token emitters plus membership prove the complete strip
half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_directPreparedTokenEmitters
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (emitters : DirectCompiledTrominoStripPreparedTokenEmitters) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_directCountedTokenEmitters membership
    (countedTokenEmitters_of_preparedTokenEmitters emitters)

end PeriodicCNFStripReduction
end LeanTrominoes


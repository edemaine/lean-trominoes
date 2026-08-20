/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenMachineBridge

/-! # Sparse prepared-token compiler interface for Theorem 5.2 -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

/-- Uniform polynomial-time emitters for the direct sparse prepared stream. -/
def DirectSparseCompiledTrominoStripPreparedTokenEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id id
        (directSparseCompiledTrominoStripPreparedTokensOfSymbols
          decider tromino))

theorem directSparseSymbolMachines_of_preparedTokenEmitters
    (emitters : DirectSparseCompiledTrominoStripPreparedTokenEmitters) :
    DirectSparseCompiledTrominoStripSymbolMachines := by
  intro Input encoding language decider tromino
  exact (emitters encoding language decider tromino).map
    (directSparseCompiledTrominoStripPolyTimeOfPreparedTokenEmitter
      decider tromino)

/-- Sparse prepared-token emitters plus the established membership theorem
prove the complete strip half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_directSparsePreparedTokenEmitters
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (emitters : DirectSparseCompiledTrominoStripPreparedTokenEmitters) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_directSparseMachines membership
    (directSparseMachines_of_symbolMachines
      (directSparseSymbolMachines_of_preparedTokenEmitters emitters))

end PeriodicCNFStripReduction
end LeanTrominoes

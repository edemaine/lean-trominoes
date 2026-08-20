/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectCountedTokenMachineBridge

/-! # Counted finite-token compiler interface for direct strip hardness -/

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

/-- Uniform finite-token emitter contract for the remaining geometric loop. -/
def DirectCompiledTrominoStripCountedTokenEmitters : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language)
      (tromino : Tromino),
    Nonempty
      (TM2ComputableInPolyTime id id
        (directCompiledTrominoStripCountedTokensOfSymbols decider tromino))

theorem executableUnaryFieldEmitters_of_countedTokenEmitters
    (emitters : DirectCompiledTrominoStripCountedTokenEmitters) :
    DirectCompiledTrominoStripExecutableUnaryFieldEmitters := by
  intro Input encoding language decider tromino
  exact (emitters encoding language decider tromino).map
    (directCompiledTrominoStripPolyTimeOfCountedTokenEmitter
      decider tromino)

/-- Counted finite-token emitters plus target membership prove the complete
strip half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_directCountedTokenEmitters
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (emitters : DirectCompiledTrominoStripCountedTokenEmitters) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_directExecutableUnaryFieldEmitters membership
    (executableUnaryFieldEmitters_of_countedTokenEmitters emitters)

end PeriodicCNFStripReduction
end LeanTrominoes

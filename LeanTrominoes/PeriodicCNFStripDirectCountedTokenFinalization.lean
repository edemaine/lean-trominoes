/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectCountedTokens

/-! # Finalization of counted direct strip tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open UnaryFieldEncoderMachine
open PeriodicCNF.UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem countAndFinalize_directCompiledTrominoStripCountedTokens
    (tromino : Tromino) (symbols : List encoding.Γ) :
    PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize
        (directCompiledTrominoStripCountedTokensOfSymbols
          decider tromino symbols) =
      let motif := directCompiledTrominoMotifOfSymbols
        decider tromino symbols
      unaryFields
        (motif.length ::
          directCompiledTrominoStripBodyFieldsOfSymbols
            decider tromino symbols) := by
  unfold directCompiledTrominoStripCountedTokensOfSymbols
  rw [CountedUnaryFieldTokens.countAndFinalize_fields_countedFieldBlocks]
  simp only [List.length_map]
  unfold directCompiledTrominoStripBodyFieldsOfSymbols
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectCountedTokenFinalization

/-! # Semantics of counted direct strip tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget
open UnaryFieldEncoderMachine
open PeriodicCNF.UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Counting motif markers, finalizing unary fields, and rotating the count
behind width and period gives the exact executable target field stream. -/
theorem rotate_countAndFinalize_directCompiledTrominoStripCountedTokens
    (tromino : Tromino) (symbols : List encoding.Γ) :
    UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo
        (PeriodicCNF.UnaryProgramTokenFinalizer.countAndFinalize
          (directCompiledTrominoStripCountedTokensOfSymbols
            decider tromino symbols)) =
      unaryFields
        (directExecutableTrominoStripFieldsOfSymbols
          decider tromino symbols) := by
  rw [countAndFinalize_directCompiledTrominoStripCountedTokens]
  unfold directCompiledTrominoStripBodyFieldsOfSymbols
  simp only [List.cons_append, List.nil_append]
  rw [UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo_unaryFields]
  rw [show directExecutableTrominoStripFieldsOfSymbols
      decider tromino symbols =
        Gadget.PeriodicOrthogonalDrawing.computablePeriodicStripFields tromino
          (directCompiledStripDrawingOfSymbols decider symbols) from rfl]
  rw [Gadget.PeriodicOrthogonalDrawing.computablePeriodicStripFields_eq]
  rw [directCompiledTrominoMotifOfSymbols_eq]
  simp only [List.cons_append, List.nil_append]

end PeriodicCNFStripReduction
end LeanTrominoes

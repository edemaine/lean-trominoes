/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenData

/-! # Exact postprocessing semantics of sparse counted tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseCountedSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Counting sparse motif markers and rotating the resulting count behind the
two target dimensions gives exactly the flat strip field stream. -/
theorem postprocess_directSparseCompiledTrominoStripCountedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    CountedUnaryFieldTokenCompiler.postprocess
        (directSparseCompiledTrominoStripCountedTokensOfSymbols
          decider tromino symbols) =
      UnaryFieldEncoderMachine.unaryFields
        (PeriodicStripFlatEncoding.stripFields
          (directSparseCompiledTrominoStripOfSymbols
            decider tromino symbols)) := by
  let target := directSparseCompiledTrominoStripOfSymbols
    decider tromino symbols
  unfold CountedUnaryFieldTokenCompiler.postprocess
  dsimp only [directSparseCompiledTrominoStripCountedTokensOfSymbols]
  rw [CountedUnaryFieldTokens.countAndFinalize_fields_countedFieldBlocks]
  simp only [List.length_map]
  simp only [List.cons_append, List.nil_append]
  rw [UnaryFieldHeaderRotation.rotateFirstFieldAfterTwo_unaryFields]
  unfold PeriodicStripFlatEncoding.stripFields
  simp only [List.flatMap, List.cons_append, List.nil_append]

end PeriodicCNFStripReduction
end LeanTrominoes

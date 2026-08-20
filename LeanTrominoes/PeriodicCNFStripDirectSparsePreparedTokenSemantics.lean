/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenData
import LeanTrominoes.PeriodicCNFStripDirectSparseTargetMotif
import LeanTrominoes.PeriodicCNFStripDirectSparseTargetPeriods

/-! # Exact semantics of direct sparse prepared tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparsePreparedSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Fixed finite expansion of the direct prepared stream is exactly the
counted-token stream of the sparse target presentation. -/
theorem expand_directSparseCompiledTrominoStripPreparedTokensOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    GadgetPixelFiniteTokens.expand
        (directSparseCompiledTrominoStripPreparedTokensOfSymbols
          decider tromino symbols) =
      directSparseCompiledTrominoStripCountedTokensOfSymbols
        decider tromino symbols := by
  unfold directSparseCompiledTrominoStripPreparedTokensOfSymbols
  rw [GadgetPixelFiniteTokens.expand_append,
    directPreparedHeaderOfSymbols_eq,
    GadgetPixelFiniteTokens.expand_append,
    GadgetPixelFiniteTokens.expand_headerField,
    GadgetPixelFiniteTokens.expand_headerField,
    GadgetSparseExpandedMotifFiniteTokens.expand_preparedSparseExpandedMotif tromino
        (directSparseAssignmentsOfSymbols decider symbols)
        (directSparseAssignmentsOfSymbols_nonnegative decider symbols)]
  dsimp only [directSparseCompiledTrominoStripCountedTokensOfSymbols]
  rw [directSparseCompiledTrominoStripOfSymbols_width,
    directSparseCompiledTrominoStripOfSymbols_period,
    directSparseCompiledTrominoStripOfSymbols_motif]
  simp [CountedUnaryFieldTokens.fields, List.append_assoc]

end PeriodicCNFStripReduction
end LeanTrominoes

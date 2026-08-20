/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentData

/-! # Exact motif of the direct sparse strip target -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseTargetMotifStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

@[simp] theorem directSparseCompiledTrominoStripOfSymbols_motif
    (tromino : Tromino) (symbols : List encoding.Γ) :
    (directSparseCompiledTrominoStripOfSymbols decider tromino symbols).motif =
      Gadget.sparseExpandedMotif tromino
        (directSparseAssignmentsOfSymbols decider symbols) := by
  unfold directSparseCompiledTrominoStripOfSymbols sparseCompiledTrominoStrip
  rw [PeriodicThreeDM.NormalizationCompiler.compileSparseStrip_motif]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

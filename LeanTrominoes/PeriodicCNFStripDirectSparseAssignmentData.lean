/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseStripCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseSymbolCompiler

/-! # Direct sparse normalization-assignment data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAssignmentDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Proof-free normalization input generated from the source symbol word. -/
def directSparseNormalizationInputOfSymbols (symbols : List encoding.Γ) :
    PeriodicThreeDM.NormalizationCompiler.Input :=
  normalizationInput
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- Nonblank normalized strip assignments in their native compiler order. -/
def directSparseAssignmentsOfSymbols (symbols : List encoding.Γ) :
    List PeriodicThreeDM.NormalizedCellAssignment :=
  PeriodicThreeDM.NormalizationCompiler.finalStripCellAssignments
    (directSparseNormalizationInputOfSymbols decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies

/-! # Raw crossover-prefix start of direct final carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartRawDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The raw duplicate-free crossover-prefix length under the original direct
variable equality. -/
def directSourceFinalCarrierRawStart
    (symbols : List encoding.Γ) : Nat :=
  (@crossoverMetadataNormalizedClausesDedup Variable
    directSourceVariableDecidableEq
      (PeriodicThreeSATThree.formula
        (directThreeCNFSourceFormula decider symbols))).length

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts

/-! # Equality-parameterized final carrier starts -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartFamilyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The generic crossover-prefix length as a named function of the equality
implementation for final direct-source variables. -/
def directSourceFinalCarrierStartFamily
    (symbols : List encoding.Γ)
    (equality : DecidableEq Variable) : Nat :=
  (@crossoverMetadataNormalizedClausesDedup Variable equality
    (PeriodicThreeSATThree.formula
      (directThreeCNFSourceFormula decider symbols))).length

end LeanTrominoes.PeriodicCNFStripReduction

end


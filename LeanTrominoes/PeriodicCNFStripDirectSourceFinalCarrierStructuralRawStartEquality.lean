/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartGenericData

/-! # Formula-base equality transport for direct carrier starts -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStructuralRawEqualityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Changing only the formula's propositionally unique base equality leaves
the structural crossover-prefix length unchanged. -/
theorem directSourceFinalCarrierStructuralRawStart_equality
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStructuralRawStartEquality decider symbols := by
  constructor
  unfold directSourceFinalCarrierStructuralRawStart
    directSourceFinalCarrierGenericRawStart
  exact congrArg
    (fun equality =>
      (@crossoverMetadataNormalizedClausesDedup Variable
        directSourceFinalStructuralVariableDecidableEq
          (@PeriodicThreeSATThree.formula (ThreeCNFVariable Nat) equality
            (directThreeCNFSourceFormula decider symbols))).length)
    (Subsingleton.elim _ _)

end LeanTrominoes.PeriodicCNFStripReduction

end

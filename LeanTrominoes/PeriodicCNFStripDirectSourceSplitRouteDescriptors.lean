/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationSemantics

/-! # Explicit route descriptors for direct strip sources -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceSplitRouteDescriptorsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The semantic numeric route stream of a direct source is the explicit
copied-incidence prefix followed by the two cycle incidences per occurrence. -/
theorem directSource_numericRouteDescriptors_eq_splitRouteDescriptors
    (symbols : List encoding.Γ) :
    numericRouteDescriptors (directSourceFormula decider symbols) =
      PeriodicThreeSATThree.splitRouteDescriptors
        (PeriodicThreeCNF.formula
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  rw [directSourceFormula_eq_threeSATThree]
  exact PeriodicThreeSATThree.numericRouteDescriptors_formula_eq_splitRouteDescriptors _

end LeanTrominoes.PeriodicCNFStripReduction

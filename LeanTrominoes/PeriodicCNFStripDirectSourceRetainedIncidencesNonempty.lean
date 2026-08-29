/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFacts

/-! # Nonempty occurrence-split incidence stream of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedIncidencesNonemptyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedIncidencesNonemptyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The occurrence-split formula of the direct width-three source has at
least one metadata incidence. -/
theorem directThreeCNFSource_retained_incidencesWithMetadata_ne_nil
    (symbols : List encoding.Γ) :
    incidencesWithMetadata
        (PeriodicThreeSATThree.formula
          (directThreeCNFSourceFormula decider symbols)) ≠ [] := by
  unfold directThreeCNFSourceFormula
  rw [← directSourceFormula_eq_threeSATThree]
  exact directSource_incidencesWithMetadata_ne_nil decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end

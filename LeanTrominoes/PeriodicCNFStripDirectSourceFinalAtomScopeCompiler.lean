/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledOccurrenceData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderAtomScopeCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct final atom-scope controls -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAtomScopeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One inherited-source or parent-local scope control per final occurrence,
in the complete canonical copied-plus-cycle order. -/
def directSourceFinalAtomScopeControls
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.AtomScopeControl :=
  HorizontalRoutedRouteHeaderAtomScope.output
    (directSourceFinalCompiledOccurrenceData decider symbols)

/-- The complete final atom-scope stream is polynomial-time computable. -/
noncomputable def directSourceFinalAtomScopeControlsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalAtomScopeControls decider) := by
  unfold directSourceFinalAtomScopeControls
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledOccurrenceDataComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderAtomScope.computableInPolyTime

/-- The compiled stream is exactly the pointwise finite scope classification
of the canonical final occurrence stream. -/
theorem directSourceFinalAtomScopeControls_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalAtomScopeControls decider symbols =
      (directSourceFinalCompiledOccurrenceData decider symbols).map
        HorizontalRoutedRouteHeader.OccurrenceData.atomScopeControl := by
  unfold directSourceFinalAtomScopeControls
  rw [HorizontalRoutedRouteHeaderAtomScope.output_eq_map]

end LeanTrominoes.PeriodicCNFStripReduction

end

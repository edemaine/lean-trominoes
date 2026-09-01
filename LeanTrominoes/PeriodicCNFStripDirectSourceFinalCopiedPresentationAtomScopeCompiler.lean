/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderPresentationAtomScopeCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct presentation-relative copied occurrence scopes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedPresentationScopeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One final copied-clause scope control per occurrence.  Inherited slots
refer to the presentation order of the matching pre-Figure9 atom words. -/
def directSourceFinalCopiedPresentationAtomScopeControls
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.AtomScopeControl :=
  HorizontalRoutedRouteHeaderPresentationAtomScope.output
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)

/-- The presentation-relative copied scope stream is polynomial-time. -/
noncomputable def
    directSourceFinalCopiedPresentationAtomScopeControlsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCopiedPresentationAtomScopeControls decider) := by
  unfold directSourceFinalCopiedPresentationAtomScopeControls
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)
    HorizontalRoutedRouteHeaderPresentationAtomScope.computableInPolyTime

/-- The remapped scope stream remains exactly aligned one-for-one with the
compiled copied occurrence-data stream. -/
theorem directSourceFinalCopiedPresentationAtomScopeControls_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedPresentationAtomScopeControls
      decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedPresentationAtomScopeControls
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderPresentationAtomScope.output_length _

end LeanTrominoes.PeriodicCNFStripReduction

end

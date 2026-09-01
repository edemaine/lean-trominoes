/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCopiedClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct copied-clause occurrence blocks and local atom equalities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedOccurrenceBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Final occurrence data for the five copied-clause families, still grouped
implicitly by the source descriptor blocks that generated them. -/
def directSourceFinalCopiedOccurrenceData
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeader.OccurrenceData :=
  HorizontalRoutedRouteHeaderOccurrenceBlock.output
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)

/-- The copied-clause occurrence-data stream is polynomial-time. -/
noncomputable def
    directSourceFinalCopiedOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCopiedOccurrenceData decider) := by
  unfold directSourceFinalCopiedOccurrenceData
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)
    HorizontalRoutedRouteHeaderOccurrenceBlock.computableInPolyTime

/-- Parent-relative final-atom equality squares for all copied clauses. -/
def directSourceFinalCopiedLocalAtomEqualityBits
    (symbols : List encoding.Γ) : List Bool :=
  HorizontalRoutedRouteHeaderOccurrenceBlock.atomEqualityBits
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)

/-- All copied-clause block-local atom equalities are polynomial-time. -/
noncomputable def
    directSourceFinalCopiedLocalAtomEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCopiedLocalAtomEqualityBits decider) := by
  unfold directSourceFinalCopiedLocalAtomEqualityBits
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)
    HorizontalRoutedRouteHeaderOccurrenceBlock.atomEqualityBitsComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

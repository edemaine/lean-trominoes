/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnData
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnCompiler

/-! # Compiling direct-atlas terminal columns of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalTerminalColumnCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compile the crossover terminal-direction prefix. -/
noncomputable def
    directSourceFinalCrossoverTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCrossoverTerminalDirectionRanks decider) :=
  RetainedFinalDirectTerminalColumns.directionRanksComputableInPolyTimeOf
    id (directRetainedFinalCrossoverClauseQueries decider)
    (directRetainedFinalCrossoverClauseQueriesComputableInPolyTime decider)

/-- Compile the crossover terminal-radial prefix. -/
noncomputable def
    directSourceFinalCrossoverTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCrossoverTerminalRadialLengths decider) :=
  RetainedFinalDirectTerminalColumns.radialLengthsComputableInPolyTimeOf
    id (directRetainedFinalCrossoverClauseQueries decider)
    (directRetainedFinalCrossoverClauseQueriesComputableInPolyTime decider)

/-- Compile the routed-clause/routed-variable terminal-direction suffix. -/
noncomputable def
    directSourceFinalRoutedTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRoutedTerminalDirectionRanks decider) :=
  RetainedFinalDirectTerminalColumns.directionRanksComputableInPolyTimeOf
    id (directRetainedFinalRoutedClauseQuerySuffix decider)
    (directRetainedFinalRoutedClauseQuerySuffixComputableInPolyTime decider)

/-- Compile the routed-clause/routed-variable terminal-radial suffix. -/
noncomputable def
    directSourceFinalRoutedTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRoutedTerminalRadialLengths decider) :=
  RetainedFinalDirectTerminalColumns.radialLengthsComputableInPolyTimeOf
    id (directRetainedFinalRoutedClauseQuerySuffix decider)
    (directRetainedFinalRoutedClauseQuerySuffixComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

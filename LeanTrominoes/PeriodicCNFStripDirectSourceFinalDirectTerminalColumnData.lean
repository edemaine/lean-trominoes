/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyData
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumn

/-! # Direct-atlas terminal columns of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Terminal directions of the retained crossover prefix. -/
def directSourceFinalCrossoverTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalDirectionRanks
    (directRetainedFinalCrossoverClauseQueries decider symbols)

/-- Terminal radial lengths of the retained crossover prefix. -/
def directSourceFinalCrossoverTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalRadialLengths
    (directRetainedFinalCrossoverClauseQueries decider symbols)

/-- Terminal directions of the routed-clause/routed-variable suffix. -/
def directSourceFinalRoutedTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalDirectionRanks
    (directRetainedFinalRoutedClauseQuerySuffix decider symbols)

/-- Terminal radial lengths of the routed-clause/routed-variable suffix. -/
def directSourceFinalRoutedTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalRadialLengths
    (directRetainedFinalRoutedClauseQuerySuffix decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end


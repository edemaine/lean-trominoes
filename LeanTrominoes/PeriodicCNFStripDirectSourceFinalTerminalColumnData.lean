/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnData

/-! # Five-family final direct-source terminal columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Bend directions followed by both direct routed-family directions. -/
def directSourceFinalBendRoutedTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  directSourceBaseBendTerminalDirectionRanks decider symbols ++
    directSourceFinalRoutedTerminalDirectionRanks decider symbols

/-- Carrier directions followed by the bend/routed suffix. -/
def directSourceFinalCarrierTerminalDirectionRankSuffix
    (symbols : List encoding.Γ) : List Nat :=
  directSourceCarrierTerminalDirectionRanks decider symbols ++
    directSourceFinalBendRoutedTerminalDirectionRanks decider symbols

/-- Complete five-family terminal-direction column. -/
def directSourceFinalTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalCrossoverTerminalDirectionRanks decider symbols ++
    directSourceFinalCarrierTerminalDirectionRankSuffix decider symbols

/-- Bend radial lengths followed by both direct routed-family lengths. -/
def directSourceFinalBendRoutedTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  directSourceBaseBendTerminalRadialLengths decider symbols ++
    directSourceFinalRoutedTerminalRadialLengths decider symbols

/-- Carrier radial lengths followed by the bend/routed suffix. -/
def directSourceFinalCarrierTerminalRadialSuffix
    (symbols : List encoding.Γ) : List Nat :=
  directSourceCarrierTerminalRadialLengths decider symbols ++
    directSourceFinalBendRoutedTerminalRadialLengths decider symbols

/-- Complete five-family terminal-radial column. -/
def directSourceFinalTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalCrossoverTerminalRadialLengths decider symbols ++
    directSourceFinalCarrierTerminalRadialSuffix decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end


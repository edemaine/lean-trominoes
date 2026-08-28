/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalColumnStreamDefinitions

/-! # Direct retained-carrier terminal-column functions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

local instance directSourceCarrierTerminalColumnDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical packed-span direction decoder on direct source symbols. -/
def directSourceCarrierTerminalDirectionStream
    (symbols : List encoding.Γ) :
    List CarrierPackedSpanTerminalColumns.Symbol :=
  CarrierPackedSpanTerminalColumns.directionRankStream
    (CarrierRankOrderedPairs.packedSpanStream
      (numericRouteDescriptors (directSourceFormula decider symbols)))

/-- Retained-carrier terminal direction ranks in global clause presentation. -/
def directSourceCarrierTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  CarrierRankOrderedPairs.retainedTerminalDirectionRanks
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- Physical packed-span radial decoder on direct source symbols. -/
def directSourceCarrierTerminalRadialStream
    (symbols : List encoding.Γ) :
    List CarrierPackedSpanTerminalColumns.Symbol :=
  CarrierPackedSpanTerminalColumns.radialLengthStream
    (CarrierRankOrderedPairs.packedSpanStream
      (numericRouteDescriptors (directSourceFormula decider symbols)))

/-- Retained-carrier terminal radial lengths in global clause presentation. -/
def directSourceCarrierTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  CarrierRankOrderedPairs.retainedTerminalRadialLengths
    (numericRouteDescriptors (directSourceFormula decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes

end

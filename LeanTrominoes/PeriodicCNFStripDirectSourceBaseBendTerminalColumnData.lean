/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData

/-! # Direct retained-bend terminal-column data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

local instance directBaseBendTerminalColumnVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical unary direction stream selected from descriptor pairs. -/
def directSourceBaseBendTerminalDirectionStream
    (symbols : List encoding.Γ) :
    List UnaryFieldEncoderMachine.Symbol :=
  RouteDescriptorPairAffine.affineBaseBendTerminalDirectionStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- Semantic direction ranks of all untranslated retained bends. -/
def directSourceBaseBendTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  (numericRouteDescriptors
    (directSourceFormula decider symbols)).flatMap fun descriptor =>
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          terminalDataDirectionRanks
            (bendRouteTerminalDataBlock
              routeBend.incomingPort routeBend.outgoingPort)

/-- Physical unary radial stream selected from descriptor pairs. -/
def directSourceBaseBendTerminalRadialStream
    (symbols : List encoding.Γ) :
    List UnaryFieldEncoderMachine.Symbol :=
  RouteDescriptorPairAffine.affineBaseBendTerminalRadialStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- Semantic radial lengths of all untranslated retained bends. -/
def directSourceBaseBendTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  (numericRouteDescriptors
    (directSourceFormula decider symbols)).flatMap fun descriptor =>
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          terminalDataRadialLengths
            (bendRouteTerminalDataBlock
              routeBend.incomingPort routeBend.outgoingPort)

end PeriodicCNFStripReduction
end LeanTrominoes

end

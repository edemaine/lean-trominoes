/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler

/-! # Compiling direct retained carrier descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCarrierCompiledStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedCarrierCompiledVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Compile exact direct-source routes, then execute the complete
rank-ordered retained carrier descriptor scan. -/
noncomputable def
    directRetainedPlanarMetadataCompiledCarrierClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledCarrierClauseDescriptorCompiler
      decider := by
  let routes := directSourceNumericRouteDescriptorsComputableInPolyTime decider
  let carriers :=
    FormulaShapeRetainedPlanarMetadataDirection.rankOrderedCarrierLinkDescriptorScanComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime routes carriers
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end

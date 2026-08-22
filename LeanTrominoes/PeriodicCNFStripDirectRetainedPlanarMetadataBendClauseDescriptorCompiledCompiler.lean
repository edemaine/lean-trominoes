/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBendClauseDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling direct retained bend descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedBendCompiledStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compile direct-source route pairs, then scan each tagged pair for its
retained bend descriptor block. -/
noncomputable def
    directRetainedPlanarMetadataCompiledBendClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataCompiledBendClauseDescriptorCompiler
      decider := by
  let fields :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let bends :=
    PeriodicOrthocrossing.RouteDescriptorPairAffine.affineBendDescriptorStreamComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime fields bends
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end

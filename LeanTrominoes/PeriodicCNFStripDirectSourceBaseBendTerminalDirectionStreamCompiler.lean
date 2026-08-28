/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendTerminalColumnCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Physical direct retained-bend terminal-direction stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBaseBendDirectionStreamStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Physical composition through tagged descriptor pairs and the finite
bend-port selector. -/
opaque directSourceBaseBendTerminalDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceBaseBendTerminalDirectionStream decider) := by
  change TM2ComputableInPolyTime id id (fun symbols : List encoding.Γ =>
    RouteDescriptorPairAffine.affineBaseBendTerminalDirectionStream
      (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider)
    RouteDescriptorPairAffine.affineBaseBendTerminalDirectionStreamComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionScalingCompiler

/-! # Direct compilation of scaled bend fallback prefixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackPrefixCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Fixed-clearance source-prefix words of every retained bend, with one
route delimiter after each of its four corner-table routes. -/
def directSourceFinalBendFallbackPrefixDirections
    (symbols : List encoding.Γ) :
    List RouteDescriptorPairAffine.BendRouteDirectionToken :=
  RouteDescriptorPairAffine.BendRoutePrefixDirectionScaling.streamOutput
    (directSourceRouteDescriptorPairFieldTags decider symbols)

/-- The complete scaled bend prefix stream is polynomial-time computable
from direct PSPACE source symbols. -/
noncomputable def
    directSourceFinalBendFallbackPrefixDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendFallbackPrefixDirections decider) := by
  unfold directSourceFinalBendFallbackPrefixDirections
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider)
    RouteDescriptorPairAffine.BendRoutePrefixDirectionScaling.streamOutputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end

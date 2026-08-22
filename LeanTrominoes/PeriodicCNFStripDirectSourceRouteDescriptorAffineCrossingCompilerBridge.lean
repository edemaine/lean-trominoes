/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorAffineCrossingCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorAffineCrossingRetainedSemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Compiler bridge for direct affine crossing markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceAffineCrossingBridgeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact direct route-descriptor crossing-marker target is
polynomial-time computable. -/
noncomputable def
    directSourceRouteDescriptorCrossingMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token
      id id (directSourceRouteDescriptorCrossingMarkers decider) :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directSourceAffineCrossingMarkers decider
      FormulaShapeDirectionOrdering.Token.variable)
    (directSourceRouteDescriptorCrossingMarkers decider)
    (directSourceAffineCrossingMarkers_eq_crossingMarkers decider)
    (directSourceAffineCrossingMarkersComputableInPolyTime decider
      FormulaShapeDirectionOrdering.Token.variable)

end PeriodicCNFStripReduction
end LeanTrominoes

end

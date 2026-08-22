/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorCrossingMarkers
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingMarkerBlocks

/-! # Nested crossing-marker blocks for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCrossingMarkerBlocksStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceCrossingMarkerBlocksVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The exact direct crossing-marker word is the flattening of the nested
descriptor-major scan blocks. -/
theorem directSourceRouteDescriptorCrossingMarkers_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorCrossingMarkers decider symbols =
      (routeDescriptorCrossingMarkerBlocks
        FormulaShapeDirectionOrdering.Token.variable
        (numericRouteDescriptors
          (directSourceFormula decider symbols))).flatten := by
  unfold directSourceRouteDescriptorCrossingMarkers
  exact (routeDescriptorCrossingMarkerBlocks_flatten
    FormulaShapeDirectionOrdering.Token.variable
    (numericRouteDescriptors
      (directSourceFormula decider symbols))).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end

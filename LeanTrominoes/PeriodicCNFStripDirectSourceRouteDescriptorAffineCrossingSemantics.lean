/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorAffineCrossingData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics

/-! # Semantics of direct affine crossing markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceAffineCrossingSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceAffineCrossingSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct compiled pair scan is exactly the verified affine crossing
stream on the direct source's numeric route descriptors. -/
theorem directSourceAffineCrossingMarkers_eq_stream
    {Marker : Type} (marker : Marker) (symbols : List encoding.Γ) :
    directSourceAffineCrossingMarkers decider marker symbols =
      RouteDescriptorPairAffine.affineCrossingMarkerStream marker
        (numericRouteDescriptors (directSourceFormula decider symbols)) := by
  unfold directSourceAffineCrossingMarkers
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  exact RouteDescriptorPairAffine.compiledAffineCrossingMarkerStream_descriptorSquare
    _ _

end PeriodicCNFStripReduction
end LeanTrominoes

end

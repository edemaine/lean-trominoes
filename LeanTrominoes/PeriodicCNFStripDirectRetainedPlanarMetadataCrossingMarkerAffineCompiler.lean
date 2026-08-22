/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorAffineCrossingCompilerBridge
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerNumericPairCompilerBridge
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Direct retained crossing-marker compiler from affine scans -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedAffineCrossingCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The affine route-descriptor scan supplies the compact numeric crossing
marker compiler boundary. -/
noncomputable def
    directRetainedPlanarMetadataCrossingNumericPairMarkersComputableInPolyTime :
    DirectRetainedPlanarMetadataCrossingNumericPairMarkerCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directSourceRouteDescriptorCrossingMarkers decider)
    (directRetainedPlanarMetadataCrossingNumericPairMarkers decider)
    (directSourceRouteDescriptorCrossingMarkers_eq_numericPairMarkers decider)
    (directSourceRouteDescriptorCrossingMarkersComputableInPolyTime decider)

/-- Hence the exact semantic retained crossing-marker stream is
polynomial-time computable. -/
noncomputable def
    directRetainedPlanarMetadataCrossingMarkersComputableInPolyTime :
    DirectRetainedPlanarMetadataCrossingMarkerCompiler decider :=
  directRetainedPlanarMetadataCrossingMarkerCompilerOfNumericPairs decider
    (directRetainedPlanarMetadataCrossingNumericPairMarkersComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end

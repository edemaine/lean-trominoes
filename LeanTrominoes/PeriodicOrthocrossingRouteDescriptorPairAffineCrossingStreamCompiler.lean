/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Polynomial-time affine crossing scan over descriptor-pair streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Run the compiled affine crossing evaluator independently on every
complete tagged descriptor-pair block. -/
def compiledAffineCrossingMarkerStream
    {Marker : Type} (marker : Marker)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Marker :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    (compiledAffineCrossingMarkers marker) tokens

/-- The independent affine crossing scan over a pair-delimited stream is
polynomial-time. -/
def compiledAffineCrossingMarkerStreamComputableInPolyTime
    {Marker : Type} [Fintype Marker] [Inhabited Marker]
    (marker : Marker) :
    TM2ComputableInPolyTime id id
      (compiledAffineCrossingMarkerStream marker) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (compiledAffineCrossingMarkersComputableInPolyTime marker) isPairEnd

@[simp] theorem compiledAffineCrossingMarkerStream_encodeDescriptorPairs
    {Marker : Type} (marker : Marker)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    compiledAffineCrossingMarkerStream marker (encodeDescriptorPairs pairs) =
      pairs.flatMap (fun pair =>
        affineCrossingMarkers marker (descriptorPairTokens pair)) := by
  unfold compiledAffineCrossingMarkerStream
  rw [mappedOutput_encodeDescriptorPairs]
  simp_rw [compiledAffineCrossingMarkers_eq]

/-- On the canonical row-major square, the compiled stream evaluator equals
the previously verified affine crossing-marker stream. -/
theorem compiledAffineCrossingMarkerStream_descriptorSquare
    {Marker : Type} (marker : Marker)
    (descriptors : List RouteDescriptor) :
    compiledAffineCrossingMarkerStream marker
        (encodeDescriptorPairs (descriptors ×ˢ descriptors)) =
      affineCrossingMarkerStream marker descriptors := by
  rw [compiledAffineCrossingMarkerStream_encodeDescriptorPairs]
  unfold affineCrossingMarkerStream affineCrossingMarkerBlocks
  exact flatMap_eq_flatten_map
    (fun pair => affineCrossingMarkers marker (descriptorPairTokens pair))
    (descriptors ×ˢ descriptors)

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

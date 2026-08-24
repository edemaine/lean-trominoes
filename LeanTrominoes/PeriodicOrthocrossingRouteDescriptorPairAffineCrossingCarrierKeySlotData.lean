/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCompiler

/-! # Fixed crossing carrier-key slots for route-descriptor pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Complete fixed crossing-key template list aligned with
`affineCrossingPredicates`. -/
def crossingCarrierKeyTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    List (List (Template (Nat × Nat × Cell))) :=
  (allRouteShapes ×ˢ allRouteShapes).flatMap
    (routeShapePairCrossingCarrierKeyTemplateBlocks pair)

/-- One activation bit per fixed affine crossing predicate. -/
def crossingCarrierKeyActivations
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  affineCrossingPredicates.map fun predicate =>
    predicate.evalTokens tokens

/-- Padded crossing carrier-key slots of one descriptor pair. -/
def paddedCrossingCarrierKeyCandidates
    (pair : RouteDescriptor × RouteDescriptor) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      (Nat × Nat × Cell)) :=
  candidates
    (crossingCarrierKeyActivations (descriptorPairTokens pair))
    (crossingCarrierKeyTemplateBlocks pair)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

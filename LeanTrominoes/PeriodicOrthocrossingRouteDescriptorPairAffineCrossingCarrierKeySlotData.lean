/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCompiler

/-! # Fixed crossing carrier-key slots for route-descriptor pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Carrier key of one affine occurrence after a fixed retention shift. -/
def Occurrence.carrierKeyAtShift
    (occurrence : Occurrence) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) (shift : Cell) :
    Nat × Nat × Cell :=
  occurrenceCarrierKey
    ((occurrence.evalPair side pair).1,
      Cell.add occurrence.translate shift)

/-- Whether shifting one neighboring occurrence by a retention shift leaves
it inside the fixed neighboring-translation window. -/
def Occurrence.carrierKeyAtShiftSupported
    (occurrence : Occurrence) (shift : Cell) : Bool :=
  decide (Cell.add occurrence.translate shift ∈ neighborTranslations)

/-- Four boundary-key templates for one retention shift: two horizontal-side
copies followed by two vertical-side copies. -/
def occurrencePairCrossingCarrierKeyShiftTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    List (Template (Nat × Nat × Cell)) :=
  let first : Template (Nat × Nat × Cell) :=
    ⟨occurrences.1.carrierKeyAtShift .first pair shift,
      occurrences.1.carrierKeyAtShiftSupported shift⟩
  let second : Template (Nat × Nat × Cell) :=
    ⟨occurrences.2.carrierKeyAtShift .second pair shift,
      occurrences.2.carrierKeyAtShiftSupported shift⟩
  [first, first, second, second]

/-- Complete retained-orbit key template block for one fixed affine
occurrence-pair crossing predicate. -/
def occurrencePairCrossingCarrierKeyTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    List (Template (Nat × Nat × Cell)) :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingCarrierKeyShiftTemplateBlock pair occurrences)

/-- Crossing-key template blocks aligned with one route-shape pair's affine
crossing predicates. -/
def routeShapePairCrossingCarrierKeyTemplateBlocks
    (pair : RouteDescriptor × RouteDescriptor)
    (shapes : RouteShape × RouteShape) :
    List (List (Template (Nat × Nat × Cell))) :=
  (shapes.1.occurrences .first ×ˢ
      shapes.2.occurrences .second).map
    (occurrencePairCrossingCarrierKeyTemplateBlock pair)

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

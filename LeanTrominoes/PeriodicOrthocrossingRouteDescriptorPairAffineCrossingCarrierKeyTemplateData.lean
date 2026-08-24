/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplates

/-! # Local crossing carrier-key templates for route-descriptor pairs -/

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

/-- For one retained crossing shift, the two first-side templates carry the
horizontal axis and the two second-side templates carry the vertical axis. -/
theorem occurrencePairCrossingCarrierKeyShiftTemplateBlock_axisDatum
    (axisValue : Bool → Nat)
    (datum : Option (Nat × Nat × Cell) → Nat)
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (firstDatum : axisValue true =
      datum (some (occurrences.1.carrierKeyAtShift .first pair shift)))
    (secondDatum : axisValue false =
      datum (some (occurrences.2.carrierKeyAtShift .second pair shift))) :
    List.Forall₂
      (fun axis template =>
        axisValue axis = datum (some template.value))
      [true, true, false, false]
      (occurrencePairCrossingCarrierKeyShiftTemplateBlock
        pair occurrences shift) := by
  unfold occurrencePairCrossingCarrierKeyShiftTemplateBlock
  dsimp only
  exact List.Forall₂.cons firstDatum
    (List.Forall₂.cons firstDatum
      (List.Forall₂.cons secondDatum
        (List.Forall₂.cons secondDatum List.Forall₂.nil)))

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

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

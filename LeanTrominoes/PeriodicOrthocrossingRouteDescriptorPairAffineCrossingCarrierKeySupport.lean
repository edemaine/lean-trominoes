/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeyTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateEvaluationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTerminalCarrierKeyMembership

/-! # Support semantics of affine crossing carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- For a matched route shape, a shifted affine occurrence key carries the
exact membership bit for that descriptor's terminal carrier-key block. -/
theorem Occurrence.carrierKeyAtShiftSupported_eq_mem_terminal
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side))
    (occurrence : Occurrence) (occurrenceMember :
      occurrence ∈ shape.occurrences side)
    (shift : Cell) :
    occurrence.carrierKeyAtShiftSupported shift =
      decide (occurrence.carrierKeyAtShift side pair shift ∈
        occurrenceTerminalCarrierKeys
          (descriptorAt pair side).selfIndexedNeighborOccurrences) := by
  have evaluatedMember :
      occurrence.evalPair side pair ∈
        (descriptorAt pair side).selfIndexedNeighborOccurrences := by
    rw [← shape.map_evalPair_occurrences side pair shapeMatches]
    exact List.mem_map.mpr
      ⟨occurrence, occurrenceMember, rfl⟩
  have keyIff := occurrenceCarrierKey_mem_selfIndexedTerminal_iff
    (descriptorAt pair side)
    (occurrence.evalPair side pair).1
    (occurrence.evalPair side pair).2
    (Cell.add occurrence.translate shift)
    evaluatedMember
  unfold Occurrence.carrierKeyAtShiftSupported
    Occurrence.carrierKeyAtShift
  exact Bool.decide_congr keyIff.symm

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

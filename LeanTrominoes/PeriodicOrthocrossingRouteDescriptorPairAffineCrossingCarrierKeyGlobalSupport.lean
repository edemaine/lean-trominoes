/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorGlobalTerminalCarrierKeyMembership
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySupport

/-! # Global support semantics of affine crossing carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- For a matched route shape whose descriptor occurs in a self-indexed
stream, a shifted affine occurrence key carries its exact global terminal-
stream membership bit. -/
theorem Occurrence.carrierKeyAtShiftSupported_eq_mem_globalTerminal
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side))
    (descriptorMember : descriptorAt pair side ∈ descriptors)
    (occurrence : Occurrence) (occurrenceMember :
      occurrence ∈ shape.occurrences side)
    (shift : Cell) :
    occurrence.carrierKeyAtShiftSupported shift =
      decide (occurrence.carrierKeyAtShift side pair shift ∈
        occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors)) := by
  have evaluatedMember :
      occurrence.evalPair side pair ∈
        (descriptorAt pair side).selfIndexedNeighborOccurrences := by
    rw [← shape.map_evalPair_occurrences side pair shapeMatches]
    exact List.mem_map.mpr
      ⟨occurrence, occurrenceMember, rfl⟩
  change occurrence.evalPair side pair ∈
      (descriptorAt pair side).neighborOccurrences
        (descriptorAt pair side).edgeIndex at evaluatedMember
  have keyIff := occurrenceCarrierKey_mem_routeDescriptorTerminal_iff
    descriptors selfIndexed (descriptorAt pair side) descriptorMember
    (occurrence.evalPair side pair).1
    (occurrence.evalPair side pair).2
    (Cell.add occurrence.translate shift)
    evaluatedMember
  unfold Occurrence.carrierKeyAtShiftSupported
    Occurrence.carrierKeyAtShift
  exact Bool.decide_congr keyIff.symm

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

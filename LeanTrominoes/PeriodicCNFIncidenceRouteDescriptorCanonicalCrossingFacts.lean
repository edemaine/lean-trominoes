/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumeration
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCrossingPairs
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # Canonical crossing facts for numeric CNF route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- Every numeric incidence descriptor stores the incidence drawing's exact
grid size, without a nonempty-stream assumption. -/
theorem numericRouteDescriptors_commonDrawingGridSize
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ∀ descriptor ∈ numericRouteDescriptors formula,
      descriptor.gridSize = drawingGridSize formula.incidenceGraph := by
  intro descriptor descriptorMember
  unfold numericRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨taggedIncidence, _taggedIncidenceMember, rfl⟩
  simp [RouteDescriptor.gridSize,
    CNFIncidence.numericRouteDescriptor, drawingGridSize]

/-- Numeric route descriptors reconstruct exactly the graph's neighboring
segment-occurrence stream. -/
theorem routeDescriptorNeighborOccurrences_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    routeDescriptorNeighborOccurrences
        (numericRouteDescriptors formula) =
      neighborOccurrences formula.incidenceGraph := by
  rw [← numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences]
  exact (incidenceGraph_neighborOccurrences_eq_numeric formula).symm

end PeriodicCNF
end LeanTrominoes

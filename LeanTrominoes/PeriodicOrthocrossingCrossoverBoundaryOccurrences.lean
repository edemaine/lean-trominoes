/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteCore
import LeanTrominoes.PlanarThreeSATCrossoverVariableOccurrences

/-! # Boundary-variable coverage of the drawing crossover family -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The fixed crossover-variable name represented by one geometric side. -/
def CrossingSide.crossoverVariable : CrossingSide → CrossoverVariable
  | .left => .aLeft
  | .right => .aRight
  | .top => .bTop
  | .bottom => .bBottom

/-- Every side variable at a canonical crossing occurs in that crossing's
fixed crossover copy. -/
theorem crossingBoundary_mem_drawingCarrierNodeCrossoverFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossings graph)
    (side : CrossingSide) :
    (Sum.inl (CarrierNode.boundary ⟨crossing, side⟩) :
        Sum CarrierNode (CrossingRecord × CrossoverInternal)) ∈
      embeddedVariableOccurrences
        (drawingCarrierNodeCrossoverFormula graph) := by
  rw [drawingCarrierNodeCrossoverFormula, crossoverFamily,
    embeddedVariableOccurrences_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨crossing,
    orientedCrossings_subset_orientedCrossingHalo graph crossingMem, ?_⟩
  rw [scopedCrossoverInstance,
    embeddedVariableOccurrences_instantiateFormula]
  apply List.mem_map.mpr
  refine ⟨side.crossoverVariable,
    crossoverVariable_mem_crossoverFormula side.crossoverVariable, ?_⟩
  cases side <;> rfl

/-- Every boundary in the canonical crossing-boundary list occurs in the
drawing crossover family. -/
theorem drawingCrossingBoundary_mem_drawingCarrierNodeCrossoverFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem : boundary ∈ drawingCrossingBoundaries graph) :
    (Sum.inl (CarrierNode.boundary boundary) :
        Sum CarrierNode (CrossingRecord × CrossoverInternal)) ∈
      embeddedVariableOccurrences
        (drawingCarrierNodeCrossoverFormula graph) := by
  unfold drawingCrossingBoundaries at boundaryMem
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨crossing, crossingMem, sideMem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sideMem
  rcases sideMem with rfl | rfl | rfl | rfl <;>
    exact crossingBoundary_mem_drawingCarrierNodeCrossoverFormula
      graph crossingMem _

end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteCore
import LeanTrominoes.PlanarThreeSATCrossoverInternalOccurrences

/-! # Internal-variable coverage of the drawing crossover family -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every internal variable at a canonical crossing occurs in the finite
drawing crossover family. -/
theorem crossoverInternal_mem_drawingCarrierNodeCrossoverFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossings graph)
    (internal : CrossoverInternal) :
    (Sum.inr (crossing, internal) :
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
  refine ⟨internal.toVariable,
    crossoverInternal_toVariable_mem_crossoverFormula internal, ?_⟩
  cases internal <;> rfl

end LeanTrominoes.PeriodicOrthocrossing

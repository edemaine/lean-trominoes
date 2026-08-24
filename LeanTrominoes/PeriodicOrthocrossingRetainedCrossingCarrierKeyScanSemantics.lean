/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingCarrierKeyShiftSemantics

/-! # Semantics of the crossing-major retained carrier-key scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Mapping retained boundary nodes to their carrier keys gives exactly the
explicit crossing/shift/side scan. -/
theorem retainedCrossingCarrierKeys_eq_scan
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedCrossingCarrierKeys graph =
      retainedCrossingCarrierKeyScan graph := by
  unfold retainedCrossingCarrierKeys retainedCrossingCarrierKeyScan
    retainedCrossingCarrierKeyBlock
    retainedCrossingBoundaries retainedCrossings
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro crossing _crossingMember
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact retainedCrossingBoundaryKeyBlock_eq_shiftBlock
    graph crossing shift

end LeanTrominoes.PeriodicOrthocrossing

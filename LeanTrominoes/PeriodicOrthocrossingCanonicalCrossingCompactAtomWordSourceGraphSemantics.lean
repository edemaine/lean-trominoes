/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordSourceData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCrossingHaloSemantics

/-! # Graph semantics of canonical crossing compact-word sources -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingCompactAtomWordSources

/-- Any descriptor stream reconstructing a graph's neighboring occurrences
also reconstructs its exact canonicalized crossing-halo order. -/
theorem crossingsAtPeriod_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (descriptors : List RouteDescriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph) :
    crossingsAtPeriod (drawingGridSize graph) descriptors =
      canonicalizedCrossingHalo graph := by
  unfold crossingsAtPeriod
  rw [occurrencesEq]
  exact occurrencePairCanonicalizedCrossingHaloAtPeriod_eq graph

end CanonicalCrossingCompactAtomWordSources
end LeanTrominoes.PeriodicOrthocrossing

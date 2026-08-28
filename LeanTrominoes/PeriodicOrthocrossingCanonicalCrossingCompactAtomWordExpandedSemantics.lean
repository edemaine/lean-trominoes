/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordExpandedData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordSourceGraphSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordSemantics

/-! # Semantics of expanded canonical crossing compact-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingCompactAtomWordSources

/-- Expanding the canonical-left source stream yields the exact compact
Figure 8(b) atom-word block for every canonical crossing. -/
theorem expandedWordsAtPeriod_eq
    {Vertex Variable : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (descriptors : List RouteDescriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph)
    (sourceWord : Variable → List Bool) :
    expandedWordsAtPeriod (drawingGridSize graph) descriptors =
      (canonicalizedCrossingHalo graph).flatMap fun crossing =>
        PlanarThreeSAT.crossoverFormula.flatMap fun clause =>
          clause.literals.map fun literal =>
            RetainedCompactAtomWords.word sourceWord
              ⟨normalizedCrossoverAtom crossing literal.1⟩ := by
  unfold expandedWordsAtPeriod wordsAtPeriod
  rw [crossingsAtPeriod_eq graph descriptors occurrencesEq]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro crossing crossingMember
  exact CrossoverCompactAtomWords.wordsForRoles_crossingPair
    sourceWord crossing

end CanonicalCrossingCompactAtomWordSources
end LeanTrominoes.PeriodicOrthocrossing

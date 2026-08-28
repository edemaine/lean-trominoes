/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordExpandedSemantics

/-! # Delimited-input semantics of canonical crossing expansion -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingCompactAtomWordSources

/-- Structure-level form of `expandedWordsAtPeriod_eq`, kept separate so
downstream direct-source proofs do not normalize the large word lists. -/
theorem expandedInputAtPeriod_eq
    {Vertex Variable : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (descriptors : List RouteDescriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph)
    (sourceWord : Variable → List Bool) :
    (⟨expandedWordsAtPeriod (drawingGridSize graph) descriptors⟩ :
        DelimitedBinaryWords.Input) =
      ⟨(canonicalizedCrossingHalo graph).flatMap fun crossing =>
        PlanarThreeSAT.crossoverFormula.flatMap fun clause =>
          clause.literals.map fun literal =>
            RetainedCompactAtomWords.word sourceWord
              ⟨normalizedCrossoverAtom crossing literal.1⟩⟩ := by
  have expanded :=
    expandedWordsAtPeriod_eq graph descriptors occurrencesEq sourceWord
  rw [expanded]

end CanonicalCrossingCompactAtomWordSources
end LeanTrominoes.PeriodicOrthocrossing

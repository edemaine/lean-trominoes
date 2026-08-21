/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumerationData
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumeration
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateSemantics

/-! # Correctness of the numeric CNF crossing occurrence-pair enumeration -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- The compact numeric segment stream reconstructs the semantic neighboring
occurrence stream exactly. -/
theorem incidenceGraph_neighborOccurrences_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    neighborOccurrences formula.incidenceGraph =
      numericNeighborOccurrences formula := by
  unfold neighborOccurrences numericNeighborOccurrences
  rw [incidenceGraph_indexedSegments_eq_numeric]

/-- The compact numeric stream and graph-free predicate reconstruct the exact
semantic canonical occurrence-pair scan. -/
theorem incidenceGraph_orientedCrossingOccurrencePairs_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    orientedCrossingOccurrencePairs formula.incidenceGraph =
      numericOrientedCrossingOccurrencePairs formula := by
  unfold orientedCrossingOccurrencePairs
    numericOrientedCrossingOccurrencePairs
    numericOrientedCrossingOccurrencePairsAtPeriod
  rw [incidenceGraph_neighborOccurrences_eq_numeric]
  apply List.filter_congr
  intro pair pairMember
  exact canonicalOrientedOccurrencePair_eq_atPeriod
    formula.incidenceGraph pair

end PeriodicCNF
end LeanTrominoes

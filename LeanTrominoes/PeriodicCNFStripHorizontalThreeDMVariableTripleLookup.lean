/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleBlockData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleLength
import LeanTrominoes.IndexedListMappedScan

/-! # Lookup of horizontal variable triples at stable prefix indices -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- A tagged member of the variable prefix is found at the same index in the
complete typed triple list. -/
theorem horizontalThreeDMVariableTriple_getElem?
    (source : PeriodicCNF Nat) (triple : Triple RoutedVariable)
    (tripleIndex : Nat)
    (member : (triple, tripleIndex) ∈
      (horizontalThreeDMVariableTriplesComputed source).zipIdx) :
    (horizontalThreeDMTypedTriplesComputed source)[tripleIndex]? =
      some triple := by
  rw [horizontalThreeDMTypedTriplesComputed_eq_blocks]
  exact IndexedListScan.append_getElem?_of_mem_zipIdx
    (horizontalThreeDMVariableTriplesComputed source)
    (horizontalThreeDMClauseTriplesZippedComputed source)
    (triple, tripleIndex) member

/-- Every stable variable-prefix index is in range for the executable
horizontal normalization input. -/
theorem horizontalThreeDMVariableTriple_indexLt
    (source : PeriodicCNF Nat) (triple : Triple RoutedVariable)
    (tripleIndex : Nat)
    (member : (triple, tripleIndex) ∈
      (horizontalThreeDMVariableTriplesComputed source).zipIdx) :
    tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length := by
  have lookup := horizontalThreeDMVariableTriple_getElem?
    source triple tripleIndex member
  have typedIndexLt := (List.getElem?_eq_some_iff.mp lookup).1
  simpa only [horizontalNormalizationInputComputed_triples_length] using
    typedIndexLt

end PeriodicCNFStripReduction
end LeanTrominoes

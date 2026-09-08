/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordKeyedValueLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceOriginalAtomWordCompiler

/-! # Original-atom coordinates selected by final compact atom keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

local instance originalCoordinateLookupVariableDecidableEq : DecidableEq Variable :=
  instDecidableEqProd

/-- Original atoms represented in the retained planar variable type. -/
def originalAtomCoordinateCandidates (source : PeriodicCNF Variable) :
    List (WrappedPeriodicPlanarSATVariable Variable) :=
  source.variableOccurrences.dedup.map fun atom => ⟨.atom atom⟩

/-- One signed coordinate field of the actual canonical planar placement. -/
def originalAtomCoordinateField (source : PeriodicCNF Variable)
    (horizontal keepPositive : Bool) (atom : WrappedPeriodicPlanarSATVariable Variable) : Nat :=
  let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).position atom
  let coordinate := if horizontal then position.1 else position.2
  if keepPositive then coordinate.toNat else (-coordinate).toNat

/-- The original-atom contribution is zero on all other constructor families. -/
def originalAtomCoordinateContribution (source : PeriodicCNF Variable)
    (horizontal keepPositive : Bool) (atom : WrappedPeriodicPlanarSATVariable Variable) : Nat :=
  if atom ∈ originalAtomCoordinateCandidates source then
    originalAtomCoordinateField source horizontal keepPositive atom
  else 0

/-- A compact original-atom key cannot alias any other atom, even outside
geometrically valid carrier inputs. -/
theorem directSourceFinalCompactAtomWord_eq_original
    (source : PeriodicCNF Variable) (query : WrappedPeriodicPlanarSATVariable Variable)
    (atom : Variable)
    (equal : directSourceFinalCompactAtomWord source query =
      directSourceFinalCompactAtomWord source ⟨.atom atom⟩) :
    query = ⟨.atom atom⟩ := by
  rcases query with ⟨query⟩
  cases query with
  | terminal indexed endpoint =>
      simp [directSourceFinalCompactAtomWord, RetainedCompactAtomWords.word] at equal
  | boundary boundary =>
      simp [directSourceFinalCompactAtomWord, RetainedCompactAtomWords.word] at equal
  | crossoverInternal internal =>
      simp [directSourceFinalCompactAtomWord, RetainedCompactAtomWords.word] at equal
  | atom other =>
      have wordsEq : DirectSourceFinalIndexedAtomWords.sourceVariableWord source other =
          DirectSourceFinalIndexedAtomWords.sourceVariableWord source atom := by
        simpa [directSourceFinalCompactAtomWord, RetainedCompactAtomWords.word] using equal
      have atomEq := directSourceFinalIndexedSourceVariableWord_injective source wordsEq
      cases atomEq
      rfl

/-- The complete keyed lookup gives exact original-atom fields in any query
order, and zero for every query outside the original-atom family. -/
theorem originalAtomCoordinateLookup_eq_contributions
    (source : PeriodicCNF Variable) (queries : List (WrappedPeriodicPlanarSATVariable Variable))
    (horizontal keepPositive : Bool) :
    DelimitedBinaryWordKeyedValueLookup.values
        ⟨queries.map (directSourceFinalCompactAtomWord source)⟩
        ⟨source.variableOccurrences.dedup.map fun atom =>
          directSourceFinalCompactAtomWord source ⟨.atom atom⟩⟩
        (source.variableOccurrences.dedup.map fun atom =>
          originalAtomCoordinateField source horizontal keepPositive ⟨.atom atom⟩) =
      queries.map (originalAtomCoordinateContribution source horizontal keepPositive) := by
  have reflects : ∀ query ∈ queries, ∀ candidate ∈ originalAtomCoordinateCandidates source,
      directSourceFinalCompactAtomWord source query =
          directSourceFinalCompactAtomWord source candidate → query = candidate := by
    intro query _queryMember candidate candidateMember equal
    obtain ⟨atom, _member, rfl⟩ := List.mem_map.mp candidateMember
    exact directSourceFinalCompactAtomWord_eq_original source query atom equal
  unfold originalAtomCoordinateContribution
  simpa [originalAtomCoordinateCandidates,
    List.map_map, Function.comp_def] using
    DelimitedBinaryWordKeyedValueLookup.values_map_keys queries
      (originalAtomCoordinateCandidates source) (directSourceFinalCompactAtomWord source)
      (originalAtomCoordinateField source horizontal keepPositive) reflects

/-- A represented original atom recovers its actual canonical coordinate. -/
theorem originalAtomCoordinateContribution_atom
    (source : PeriodicCNF Variable) (horizontal keepPositive : Bool) (atom : Variable)
    (member : atom ∈ source.variableOccurrences.dedup) :
    originalAtomCoordinateContribution source horizontal keepPositive ⟨.atom atom⟩ =
      originalAtomCoordinateField source horizontal keepPositive ⟨.atom atom⟩ := by
  apply if_pos
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

/-- Every non-original constructor contributes zero to this coordinate column. -/
theorem originalAtomCoordinateContribution_of_not_original
    (source : PeriodicCNF Variable) (horizontal keepPositive : Bool)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (notOriginal : ∀ atom, query ≠ ⟨.atom atom⟩) :
    originalAtomCoordinateContribution source horizontal keepPositive query = 0 := by
  apply if_neg
  intro member
  obtain ⟨atom, _member, equal⟩ := List.mem_map.mp member
  exact notOriginal atom equal.symm

end LeanTrominoes.PeriodicCNFStripReduction

end

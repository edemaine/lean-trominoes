/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPreFigureNineInheritedRingAtomCodeNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedRingAtomCodeBlockSemantics

/-! # Numeric identities of actual retained source ring variables -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance inheritedRingSemanticStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance inheritedRingSemanticVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem compactWord_mem_of_atom_mem
    (symbols : List encoding.Γ) (atom : WrappedPeriodicPlanarSATVariable Variable)
    (member : atom ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences) :
    directSourceFinalCompactAtomWord (directSourceFormula decider symbols) atom ∈
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words := by
  rw [← allOccurrenceVariables_fst] at member
  obtain ⟨copy, copyMember, atomEq⟩ := List.mem_map.mp member
  have wordMember := directSourceFinalCompactOccurrenceAtomWords_mem decider symbols copy copyMember
  rwa [atomEq] at wordMember

/-- The last-index numeric identity separates all actual retained source
atoms, including atoms used by the implication-cycle suffix. -/
theorem directSourceFinalCompactAtomIdentityDatum_eq_iff_atom
    (symbols : List encoding.Γ) (first second : WrappedPeriodicPlanarSATVariable Variable)
    (firstMember : first ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences)
    (secondMember : second ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences) :
    directSourceFinalCompactAtomIdentityDatum decider symbols
        (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) first) =
      directSourceFinalCompactAtomIdentityDatum decider symbols
        (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) second) ↔
      first = second := by
  constructor
  · intro identitiesEq
    have wordsEq := (LastTrueUnaryValueLookupMachine.lookup_equalityRow_range_eq_iff
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words
      (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) first)
      (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) second)
      (compactWord_mem_of_atom_mem decider symbols first firstMember)
      (compactWord_mem_of_atom_mem decider symbols second secondMember)).mp (by
        simpa only [directSourceFinalCompactAtomIdentityDatum, LastRepresentativeEqualityRows.equalityRow,
          StableOccurrenceRanks.equalityRow] using identitiesEq)
    exact directSourceFinalCompactOccurrenceAtomWords_separate decider symbols
      first firstMember second secondMember wordsEq
  · intro atomsEq
    rw [atomsEq]

/-- Common numeric identity of a retained source atom and one of its nine
ring vertices. Both copied and cycle inherited codes use this namespace. -/
noncomputable def directSourceFinalInheritedRingCode
    (symbols : List encoding.Γ) (atom : WrappedPeriodicPlanarSATVariable Variable) (slot : Nat) : Nat :=
  inheritedRingAtomCode
    (directSourceFinalCompactAtomIdentityDatum decider symbols
      (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) atom)) slot

/-- On represented source atoms and genuine ring slots, numeric equality is
exactly equality of the actual fixed-ring copy variables. -/
theorem directSourceFinalInheritedRingCode_eq_iff
    (symbols : List encoding.Γ) (first second : WrappedPeriodicPlanarSATVariable Variable)
    (firstMember : first ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences)
    (secondMember : second ∈ (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.variableOccurrences)
    (firstSlot secondSlot : Nat)
    (firstSlotLt : firstSlot < fixedEightRingVertexCount)
    (secondSlotLt : secondSlot < fixedEightRingVertexCount) :
    directSourceFinalInheritedRingCode decider symbols first firstSlot =
        directSourceFinalInheritedRingCode decider symbols second secondSlot ↔
      ((first, firstSlot, 0) : ThreeOccurrenceVariable _) = (second, secondSlot, 0) := by
  rw [directSourceFinalInheritedRingCode, directSourceFinalInheritedRingCode,
    inheritedRingAtomCode_eq_iff _ _ _ _ firstSlotLt secondSlotLt,
    directSourceFinalCompactAtomIdentityDatum_eq_iff_atom decider symbols first second firstMember secondMember]
  simp only [Prod.mk.injEq, and_true]

/-- The pre-Figure 9 candidate column applies the same ring-code function to
its actual semantic atom and bounded stable-rank pairs. -/
theorem directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_semantic_pairs
    (symbols : List encoding.Γ) :
    directSourceFinalPreFigureNineInheritedRingAtomCodes decider symbols =
      (retainedOccurrenceGlobalBoundedStableAtomRankPairs
        (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes (directSourceFormula decider symbols))).map
        (fun pair => directSourceFinalInheritedRingCode decider symbols pair.1 pair.2) := by
  rw [directSourceFinalPreFigureNineInheritedRingAtomCodes,
    directSourceFinalPreFigureNineInheritedAtomPairs_eq_map, List.map_map]
  simp only [Function.comp_def, directSourceFinalInheritedRingCode]

/-- Every copied inherited code is an ordinary lookup in that same semantic
candidate column at its compiled source-presentation position. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_map_getD_semantic_pairs
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      (directSourceFinalCopiedSourcePositions decider symbols).map fun position =>
        ((retainedOccurrenceGlobalBoundedStableAtomRankPairs
          (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
          (retainedFinalCoordinatedScaledSourceRoutes (directSourceFormula decider symbols))).map
          (fun pair => directSourceFinalInheritedRingCode decider symbols pair.1 pair.2)).getD position 0 := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_selectedValues,
    HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_eq_map_getD _ _
      (directSourceFinalPreFigureNineInheritedRingAtomCodes_length_eq_total decider symbols),
    directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_semantic_pairs]
  rfl

/-- Distinct compact identities follow the actual retained source-variable
order used to instantiate the implication cycles. -/
theorem directSourceFinalDistinctAtomIdentityIndices_eq_actual_atoms
    (symbols : List encoding.Γ) :
    directSourceFinalDistinctAtomIdentityIndices decider symbols =
      ((retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase.variableOccurrences.dedup).map
        (fun atom => directSourceFinalCompactAtomIdentityDatum decider symbols
          (directSourceFinalCompactAtomWord (directSourceFormula decider symbols) atom)) := by
  rw [directSourceFinalDistinctAtomIdentityIndices_eq_dedup_map]
  unfold directSourceFinalCompactOccurrenceAtomWords
  rw [retainedOccurrenceGlobalAtomWords_dedup_eq _ _
    (directSourceFinalCompactOccurrenceAtomWords_separate decider symbols), List.map_map]
  simp only [Function.comp_def]

/-- Every cycle code uses its actual retained source atom and the fixed local
ring slot, in precisely the source-variable order of the cycle construction. -/
theorem directSourceFinalCycleInheritedRingAtomCodes_eq_actual_atoms
    (symbols : List encoding.Γ) :
    directSourceFinalCycleInheritedRingAtomCodes decider symbols =
      ((retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase.variableOccurrences.dedup).flatMap
        (fun atom => directSourceFinalLocalCycleRingVertexSlots.map
          (fun slot => directSourceFinalInheritedRingCode decider symbols atom slot.val)) := by
  rw [directSourceFinalCycleInheritedRingAtomCodes_eq_flatMap,
    directSourceFinalDistinctAtomIdentityIndices_eq_actual_atoms, List.flatMap_map]
  simp only [List.map_map, Function.comp_def, directSourceFinalInheritedRingCode]

end LeanTrominoes.PeriodicCNFStripReduction

end

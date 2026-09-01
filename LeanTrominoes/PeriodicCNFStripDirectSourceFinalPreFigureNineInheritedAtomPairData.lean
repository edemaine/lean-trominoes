/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedTerminalSlotCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDistinctAtomIdentitySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.RetainedAngularOccurrenceGlobalBoundedStableRankPairNodup

/-! # Direct pre-Figure9 inherited atom-pair data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

set_option maxHeartbeats 800000

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

local instance directPreFigureNineInheritedPairDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Numeric compact-atom identity paired with bounded terminal slot at every
pre-Figure9 direct occurrence. -/
def directSourceFinalPreFigureNineInheritedAtomPairs
    (symbols : List encoding.Γ) : List (Nat × Nat) :=
  List.zipWith Prod.mk
    (directSourceFinalCompactOccurrenceAtomIdentityIndices decider symbols)
    (directSourceFinalTerminalSlotValues decider symbols)

private theorem zipWith_map_map
    {Value First Second : Type} (values : List Value)
    (first : Value → First) (second : Value → Second) :
    List.zipWith Prod.mk (values.map first) (values.map second) =
      values.map fun value => (first value, second value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp [induction]

/-- Last-index identities of abstract occurrence atom words are pointwise
lookups over the occurrence presentation. -/
private theorem retainedOccurrenceGlobalAtomIdentityIndices_eq_map
    {Atom : Type*} (source : PeriodicCNF Atom)
    (atomWord : Atom → List Bool) :
    DelimitedBinaryWordLastIndexIdentity.identityIndices
        (retainedOccurrenceGlobalAtomWords source atomWord) =
      (allOccurrenceVariables source).map fun copy =>
        LastTrueUnaryValueLookupMachine.lookup
          (LastRepresentativeEqualityRows.equalityRow
            (retainedOccurrenceGlobalAtomWords source atomWord).words
            (atomWord copy.1))
          (List.range
            (retainedOccurrenceGlobalAtomWords source atomWord).words.length) := by
  rw [DelimitedBinaryWordLastIndexIdentity.identityIndices_eq_map]
  unfold retainedOccurrenceGlobalAtomWords
  rw [List.map_map]
  rfl

/-- The direct compact identity compiler is the semantic atom-word lookup
mapped over the pre-Figure9 occurrence presentation. -/
private theorem directSourceFinalCompactOccurrenceAtomIdentityIndices_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalCompactOccurrenceAtomIdentityIndices decider symbols =
      (allOccurrenceVariables
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase).map fun copy =>
            directSourceFinalCompactAtomIdentityDatum decider symbols
              (directSourceFinalCompactAtomWord
                (directSourceFormula decider symbols) copy.1) := by
  unfold directSourceFinalCompactOccurrenceAtomIdentityIndices
    directSourceFinalCompactOccurrenceAtomWords
  rw [retainedOccurrenceGlobalAtomIdentityIndices_eq_map]
  apply List.map_congr_left
  intro copy copyMember
  unfold directSourceFinalCompactAtomIdentityDatum
    directSourceFinalCompactOccurrenceAtomWords
  rfl

/-- Abstract bounded stable slots, projected to naturals, are pointwise the
bounded stable-rank function on the occurrence presentation. -/
private theorem retainedOccurrenceGlobalBoundedSlotValues_eq_map
    {Atom : Type*} [DecidableEq Atom]
    (source : PeriodicCNF Atom)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    FiniteUnaryFieldMap.values Fin.val
        (BoundedRetainedTerminalSlots.slots
          (retainedOccurrenceGlobalStableTerminalRanks source routes)) =
      (allOccurrenceVariables source).map fun copy =>
        (boundedRetainedTerminalSlot
          (retainedOccurrenceGlobalStableTerminalRank
            source routes copy)).val := by
  unfold FiniteUnaryFieldMap.values BoundedRetainedTerminalSlots.slots
  rw [retainedOccurrenceGlobalStableTerminalRanks_eq_map]
  simp only [List.map_map, Function.comp_def]

/-- The direct terminal-slot compiler is the bounded global stable rank
mapped over the same pre-Figure9 occurrence presentation. -/
private theorem directSourceFinalTerminalSlotValues_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalSlotValues decider symbols =
      (allOccurrenceVariables
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase).map fun copy =>
            (boundedRetainedTerminalSlot
              (retainedOccurrenceGlobalStableTerminalRank
                (retainedFinalCoordinatedScaledSource
                  (directSourceFormula decider symbols)).erase
                (retainedFinalCoordinatedScaledSourceRoutes
                  (directSourceFormula decider symbols)) copy)).val := by
  unfold directSourceFinalTerminalSlotValues
  exact retainedOccurrenceGlobalBoundedSlotValues_eq_map _ _

/-- The compiled pre-Figure9 pair column is the semantic bounded atom/rank
presentation with compact numeric identity applied to its atom component. -/
theorem directSourceFinalPreFigureNineInheritedAtomPairs_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalPreFigureNineInheritedAtomPairs decider symbols =
      (retainedOccurrenceGlobalBoundedStableAtomRankPairs
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes
          (directSourceFormula decider symbols))).map fun pair =>
            (directSourceFinalCompactAtomIdentityDatum decider symbols
              (directSourceFinalCompactAtomWord
                (directSourceFormula decider symbols) pair.1),
              pair.2) := by
  unfold directSourceFinalPreFigureNineInheritedAtomPairs
  rw [directSourceFinalCompactOccurrenceAtomIdentityIndices_eq_map,
    directSourceFinalTerminalSlotValues_eq_map, zipWith_map_map]
  unfold retainedOccurrenceGlobalBoundedStableAtomRankPairs
  rw [List.map_map]
  apply List.map_congr_left
  intro copy copyMember
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end

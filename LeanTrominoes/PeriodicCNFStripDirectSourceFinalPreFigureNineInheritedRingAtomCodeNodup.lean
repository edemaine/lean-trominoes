/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedRingAtomCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPreFigureNineInheritedAtomPairNodup

/-! # Duplicate-free direct pre-Figure9 inherited ring codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

set_option maxHeartbeats 800000

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

local instance directPreFigureNineInheritedRingCodeVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Base-nine inherited ring codes for the entire pre-Figure9 occurrence
presentation, before copied clauses select their inherited positions. -/
def directSourceFinalPreFigureNineInheritedRingAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalPreFigureNineInheritedAtomPairs
    decider symbols).map fun pair =>
      inheritedRingAtomCode pair.1 pair.2

private theorem map_zipWith_mk
    {First Second Output : Type*}
    (mapPair : First × Second → Output)
    (first : List First) (second : List Second) :
    (List.zipWith Prod.mk first second).map mapPair =
      List.zipWith (fun left right => mapPair (left, right)) first second := by
  induction first generalizing second with
  | nil => rfl
  | cons value values induction =>
      cases second with
      | nil => rfl
      | cons other others => simp [induction]

/-- The candidate code list is exactly the pointwise base-nine zip of the
compact identity and bounded terminal-slot compiler columns. -/
theorem directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalPreFigureNineInheritedRingAtomCodes decider symbols =
      List.zipWith inheritedRingAtomCode
        (directSourceFinalCompactOccurrenceAtomIdentityIndices decider symbols)
        (directSourceFinalTerminalSlotValues decider symbols) := by
  unfold directSourceFinalPreFigureNineInheritedRingAtomCodes
    directSourceFinalPreFigureNineInheritedAtomPairs
  exact map_zipWith_mk _ _ _

/-- The pre-Figure9 candidate code list has exactly the source arity consumed
by copied Figure 9 blocks. -/
theorem directSourceFinalPreFigureNineInheritedRingAtomCodes_length_eq_total
    (symbols : List encoding.Γ) :
    (directSourceFinalPreFigureNineInheritedRingAtomCodes
      decider symbols).length =
      HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount
        (directRetainedFigureNineCopiedClauseDescriptors
          decider symbols) := by
  rw [directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_zipWith,
    List.length_zipWith,
    directSourceFinalCompactOccurrenceAtomIdentityIndices_length_eq_total,
    directSourceFinalTerminalSlotValues_length_eq_total]
  exact Nat.min_self _

/-- Every semantic bounded stable slot lies below the nine-vertex ring base. -/
private theorem retainedOccurrenceGlobalBoundedStableAtomRankPairs_slot_lt
    {Atom : Type*} [DecidableEq Atom]
    (source : PeriodicCNF Atom)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    ∀ pair ∈ retainedOccurrenceGlobalBoundedStableAtomRankPairs source routes,
      pair.2 < fixedEightRingVertexCount := by
  intro pair pairMember
  unfold retainedOccurrenceGlobalBoundedStableAtomRankPairs at pairMember
  rcases List.mem_map.mp pairMember with ⟨copy, copyMember, rfl⟩
  have slotLt := (boundedRetainedTerminalSlot
    (retainedOccurrenceGlobalStableTerminalRank source routes copy)).isLt
  simp only [fixedEightRingVertexCount]
  omega

/-- Every compiled pre-Figure9 inherited pair uses a genuine base-nine slot. -/
private theorem directSourceFinalPreFigureNineInheritedAtomPairs_slot_lt
    (symbols : List encoding.Γ) :
    ∀ pair ∈ directSourceFinalPreFigureNineInheritedAtomPairs decider symbols,
      pair.2 < fixedEightRingVertexCount := by
  rw [directSourceFinalPreFigureNineInheritedAtomPairs_eq_map]
  intro pair pairMember
  rcases List.mem_map.mp pairMember with
    ⟨semanticPair, semanticPairMember, rfl⟩
  exact retainedOccurrenceGlobalBoundedStableAtomRankPairs_slot_lt
    _ _ semanticPair semanticPairMember

private theorem map_nodup_of_injective_on
    {Value Output : Type*} (mapValue : Value → Output)
    (values : List Value) (valuesNodup : values.Nodup)
    (injectiveOn : ∀ first ∈ values, ∀ second ∈ values,
      mapValue first = mapValue second → first = second) :
    (values.map mapValue).Nodup := by
  induction values with
  | nil => simp
  | cons value values induction =>
      rw [List.nodup_cons] at valuesNodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro mappedMember
        rcases List.mem_map.mp mappedMember with
          ⟨later, laterMember, mappedEq⟩
        have valueEq := injectiveOn value (by simp) later
          (by simp [laterMember]) mappedEq.symm
        exact valuesNodup.1 (valueEq ▸ laterMember)
      · apply induction valuesNodup.2
        intro first firstMember second secondMember equality
        exact injectiveOn first (by simp [firstMember])
          second (by simp [secondMember]) equality

/-- Base-nine encoding preserves duplicate-freedom of the complete direct
pre-Figure9 inherited candidate column. -/
theorem directSourceFinalPreFigureNineInheritedRingAtomCodes_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalPreFigureNineInheritedRingAtomCodes
      decider symbols).Nodup := by
  unfold directSourceFinalPreFigureNineInheritedRingAtomCodes
  apply map_nodup_of_injective_on _ _
    (directSourceFinalPreFigureNineInheritedAtomPairs_nodup decider symbols)
  intro first firstMember second secondMember encodedEq
  have componentsEq := (inheritedRingAtomCode_eq_iff
    first.1 second.1 first.2 second.2
    (directSourceFinalPreFigureNineInheritedAtomPairs_slot_lt
      decider symbols first firstMember)
    (directSourceFinalPreFigureNineInheritedAtomPairs_slot_lt
      decider symbols second secondMember)).mp encodedEq
  exact Prod.ext componentsEq.1 componentsEq.2

end PeriodicCNFStripReduction
end LeanTrominoes

end

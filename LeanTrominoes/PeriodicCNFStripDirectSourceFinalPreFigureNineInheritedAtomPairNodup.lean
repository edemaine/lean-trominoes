/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPreFigureNineInheritedAtomPairData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledSourceOccurrenceBound

/-! # Duplicate-free direct pre-Figure9 inherited atom pairs -/

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

local instance directPreFigureNineInheritedPairVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

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

/-- Compact numeric identity together with bounded slot is injective on the
semantic pre-Figure9 occurrence-pair presentation. -/
private theorem directSourceFinalPreFigureNineInheritedAtomPairMap_injectiveOn
    (symbols : List encoding.Γ) :
    let source :=
      (retainedFinalCoordinatedScaledSource
        (directSourceFormula decider symbols)).erase
    let routes := retainedFinalCoordinatedScaledSourceRoutes
      (directSourceFormula decider symbols)
    let atomWord := directSourceFinalCompactAtomWord
      (directSourceFormula decider symbols)
    let semanticPairs :=
      retainedOccurrenceGlobalBoundedStableAtomRankPairs source routes
    ∀ first ∈ semanticPairs, ∀ second ∈ semanticPairs,
      (directSourceFinalCompactAtomIdentityDatum decider symbols
          (atomWord first.1), first.2) =
        (directSourceFinalCompactAtomIdentityDatum decider symbols
          (atomWord second.1), second.2) →
      first = second := by
  dsimp only
  let source :=
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase
  let atomWord := directSourceFinalCompactAtomWord
    (directSourceFormula decider symbols)
  intro first firstMember second secondMember encodedEq
  have identityEq := congrArg (fun pair : Nat × Nat => pair.1) encodedEq
  have slotEq := congrArg (fun pair : Nat × Nat => pair.2) encodedEq
  rcases List.mem_map.mp firstMember with
    ⟨firstCopy, firstCopyMember, firstEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondCopy, secondCopyMember, secondEq⟩
  have firstAtomMember : first.1 ∈ source.variableOccurrences := by
    rw [← allOccurrenceVariables_fst]
    exact List.mem_map.mpr ⟨firstCopy, firstCopyMember,
      congrArg Prod.fst firstEq⟩
  have secondAtomMember : second.1 ∈ source.variableOccurrences := by
    rw [← allOccurrenceVariables_fst]
    exact List.mem_map.mpr ⟨secondCopy, secondCopyMember,
      congrArg Prod.fst secondEq⟩
  have firstWordMember : atomWord first.1 ∈
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words := by
    have copyWordMember :=
      directSourceFinalCompactOccurrenceAtomWords_mem
        decider symbols firstCopy firstCopyMember
    rw [congrArg Prod.fst firstEq] at copyWordMember
    exact copyWordMember
  have secondWordMember : atomWord second.1 ∈
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words := by
    have copyWordMember :=
      directSourceFinalCompactOccurrenceAtomWords_mem
        decider symbols secondCopy secondCopyMember
    rw [congrArg Prod.fst secondEq] at copyWordMember
    exact copyWordMember
  have wordEq : atomWord first.1 = atomWord second.1 := by
    unfold directSourceFinalCompactAtomIdentityDatum at identityEq
    exact (LastTrueUnaryValueLookupMachine.lookup_equalityRow_range_eq_iff
      (directSourceFinalCompactOccurrenceAtomWords decider symbols).words
      (atomWord first.1) (atomWord second.1)
      firstWordMember secondWordMember).mp (by
        simpa [LastRepresentativeEqualityRows.equalityRow,
          StableOccurrenceRanks.equalityRow] using identityEq)
  have atomEq : first.1 = second.1 :=
    (directSourceFinalCompactOccurrenceAtomWords_separate decider symbols)
      first.1 firstAtomMember second.1 secondAtomMember wordEq
  exact Prod.ext atomEq slotEq

/-- The actual numeric compact identities and bounded terminal slots form a
duplicate-free pre-Figure9 inherited candidate column. -/
theorem directSourceFinalPreFigureNineInheritedAtomPairs_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalPreFigureNineInheritedAtomPairs
      decider symbols).Nodup := by
  let source :=
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase
  let routes := retainedFinalCoordinatedScaledSourceRoutes
    (directSourceFormula decider symbols)
  let atomWord := directSourceFinalCompactAtomWord
    (directSourceFormula decider symbols)
  let semanticPairs :=
    retainedOccurrenceGlobalBoundedStableAtomRankPairs source routes
  rw [directSourceFinalPreFigureNineInheritedAtomPairs_eq_map]
  apply map_nodup_of_injective_on _ semanticPairs
  · exact retainedOccurrenceGlobalBoundedStableAtomRankPairs_nodup
      source routes
        (directSourceFinalScaledSource_occurrencesAtMostEight decider symbols)
  exact directSourceFinalPreFigureNineInheritedAtomPairMap_injectiveOn
    decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end

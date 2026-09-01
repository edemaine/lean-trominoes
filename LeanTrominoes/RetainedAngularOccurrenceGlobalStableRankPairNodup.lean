/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRank
import LeanTrominoes.RetainedAngularOccurrenceStableRank

/-! # Uniqueness of global stable atom/rank pairs -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Semantic atom and stable terminal rank at every global occurrence. -/
def retainedOccurrenceGlobalStableAtomRankPairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    List (Variable × Nat) :=
  (allOccurrenceVariables source).map fun copy =>
    (copy.1,
      retainedOccurrenceGlobalStableTerminalRank source routes copy)

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

/-- Stable ranking is injective inside each semantic atom fiber, so pairing
every occurrence's atom with its global stable rank removes all duplicates. -/
theorem retainedOccurrenceGlobalStableAtomRankPairs_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableAtomRankPairs source routes).Nodup := by
  unfold retainedOccurrenceGlobalStableAtomRankPairs
  apply map_nodup_of_injective_on _ _
    (allOccurrenceVariables_nodup source)
  intro first firstMember second secondMember pairEq
  have atomEq : first.1 = second.1 :=
    congrArg (fun pair : Variable × Nat => pair.1) pairEq
  have rankEq :
      retainedOccurrenceGlobalStableTerminalRank source routes first =
        retainedOccurrenceGlobalStableTerminalRank source routes second :=
    congrArg Prod.snd pairEq
  let atom := first.1
  let fiber := occurrenceVariables source atom
  let ordered := StableListRanks.valuesByStableLowerRank
    (retainedOccurrenceTerminalCoordinate routes) fiber
  have firstFiber : first ∈ fiber := by
    dsimp [fiber]
    rw [occurrenceVariables_eq_filter]
    simp [firstMember, atom]
  have secondFiber : second ∈ fiber := by
    dsimp [fiber]
    rw [occurrenceVariables_eq_filter]
    simp [secondMember, atom, atomEq]
  have firstRank :
      retainedOccurrenceGlobalStableTerminalRank source routes first =
        ordered.idxOf first := by
    calc
      _ = retainedOccurrenceStableTerminalRank
          source routes atom first :=
        (retainedOccurrenceStableTerminalRank_eq_global
          source routes atom first firstFiber).symm
      _ = ordered.idxOf first := by
        exact StableListRanks.selectedIndexedLowerRank_true_eq_idxOf_valuesByStableLowerRank
          (retainedOccurrenceTerminalCoordinate routes)
          fiber (occurrenceVariables_nodup source atom)
          first firstFiber
  have secondRank :
      retainedOccurrenceGlobalStableTerminalRank source routes second =
        ordered.idxOf second := by
    calc
      _ = retainedOccurrenceStableTerminalRank
          source routes atom second :=
        (retainedOccurrenceStableTerminalRank_eq_global
          source routes atom second secondFiber).symm
      _ = ordered.idxOf second := by
        exact StableListRanks.selectedIndexedLowerRank_true_eq_idxOf_valuesByStableLowerRank
          (retainedOccurrenceTerminalCoordinate routes)
          fiber (occurrenceVariables_nodup source atom)
          second secondFiber
  have orderedFirst : first ∈ ordered := by
    dsimp [ordered]
    rw [StableListRanks.valuesByStableLowerRank_eq_insertionSort]
    exact (List.mem_insertionSort
      (r := fun first second : ThreeOccurrenceVariable Variable =>
        retainedOccurrenceTerminalCoordinate routes first <=
          retainedOccurrenceTerminalCoordinate routes second)).mpr firstFiber
  have orderedSecond : second ∈ ordered := by
    dsimp [ordered]
    rw [StableListRanks.valuesByStableLowerRank_eq_insertionSort]
    exact (List.mem_insertionSort
      (r := fun first second : ThreeOccurrenceVariable Variable =>
        retainedOccurrenceTerminalCoordinate routes first <=
          retainedOccurrenceTerminalCoordinate routes second)).mpr secondFiber
  have indexEq : ordered.idxOf first = ordered.idxOf second := by
    rw [← firstRank, ← secondRank]
    exact rankEq
  have firstAt : ordered[ordered.idxOf first]? = some first :=
    List.getElem?_idxOf orderedFirst
  have secondAt : ordered[ordered.idxOf second]? = some second :=
    List.getElem?_idxOf orderedSecond
  rw [indexEq] at firstAt
  exact Option.some.inj (firstAt.symm.trans secondAt)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

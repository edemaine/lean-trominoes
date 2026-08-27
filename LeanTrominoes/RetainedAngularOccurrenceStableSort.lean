/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PrimrecListSort
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinate
import LeanTrominoes.StableListRankEnumerationSemantics

/-! # Stable numeric sorting of retained angular occurrences -/

namespace LeanTrominoes

private theorem orderedInsert_eq_of_rel_iff_on
    {Item : Type*}
    {firstRelation secondRelation : Item → Item → Prop}
    [DecidableRel firstRelation] [DecidableRel secondRelation]
    (value : Item) (values : List Item)
    (agree : ∀ other ∈ values,
      firstRelation value other ↔ secondRelation value other) :
    values.orderedInsert firstRelation value =
      values.orderedInsert secondRelation value := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases relation : firstRelation value head
      · rw [List.orderedInsert_cons_of_le firstRelation tail relation]
        rw [List.orderedInsert_cons_of_le secondRelation tail
          ((agree head List.mem_cons_self).mp relation)]
      · rw [List.orderedInsert_of_not_le firstRelation tail relation]
        rw [List.orderedInsert_of_not_le secondRelation tail fun second =>
          relation ((agree head List.mem_cons_self).mpr second)]
        congr 1
        exact induction fun other otherMember =>
          agree other (List.mem_cons_of_mem head otherMember)

private theorem insertionSort_eq_of_rel_iff_on
    {Item : Type*}
    (firstRelation secondRelation : Item → Item → Prop)
    [DecidableRel firstRelation] [DecidableRel secondRelation]
    (items : List Item)
    (agree : ∀ first ∈ items, ∀ second ∈ items,
      firstRelation first second ↔ secondRelation first second) :
    items.insertionSort firstRelation =
      items.insertionSort secondRelation := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.insertionSort_cons]
      rw [induction fun first firstMember second secondMember =>
        agree first (List.mem_cons_of_mem head firstMember)
          second (List.mem_cons_of_mem head secondMember)]
      apply orderedInsert_eq_of_rel_iff_on
      intro other otherMember
      exact agree head List.mem_cons_self other
        (List.mem_cons_of_mem head
          ((List.mem_insertionSort (r := secondRelation)).mp otherMember))

/-- Stable Boolean sorting depends only on comparisons between values that
actually occur in the input list. -/
private theorem boolStableSort_eq_of_eq_on
    {Item : Type*}
    (firstLE secondLE : Item → Item → Bool)
    (items : List Item)
    (agree : ∀ first ∈ items, ∀ second ∈ items,
      firstLE first second = secondLE first second) :
    Computability.boolStableSort firstLE items =
      Computability.boolStableSort secondLE items := by
  let firstRelation : (Item × Nat) → (Item × Nat) → Prop :=
    fun first second => List.zipIdxLE firstLE first second = true
  let secondRelation : (Item × Nat) → (Item × Nat) → Prop :=
    fun first second => List.zipIdxLE secondLE first second = true
  unfold Computability.boolStableSort
  rw [Computability.boolInsertionSort_eq_insertionSort
    (List.zipIdxLE firstLE) firstRelation (fun _ _ => Iff.rfl)]
  rw [Computability.boolInsertionSort_eq_insertionSort
    (List.zipIdxLE secondLE) secondRelation (fun _ _ => Iff.rfl)]
  apply congrArg (List.map Prod.fst)
  apply insertionSort_eq_of_rel_iff_on
  rintro ⟨first, firstIndex⟩ firstMember
    ⟨second, secondIndex⟩ secondMember
  have firstOriginal : first ∈ items :=
    List.fst_mem_of_mem_zipIdx firstMember
  have secondOriginal : second ∈ items :=
    List.fst_mem_of_mem_zipIdx secondMember
  have forward := agree first firstOriginal second secondOriginal
  have reverse := agree second secondOriginal first firstOriginal
  simp only [firstRelation, secondRelation]
  rw [show List.zipIdxLE firstLE (first, firstIndex)
          (second, secondIndex) =
        List.zipIdxLE secondLE (first, firstIndex)
          (second, secondIndex) by
    simp [List.zipIdxLE, forward, reverse]]

/-- Stable sorting by a decided linear-order coordinate is exactly the
existing stable lower-rank enumeration. -/
private theorem boolStableSort_decideLE_eq_valuesByStableLowerRank
    {Item Coordinate : Type*} [LinearOrder Coordinate]
    (coordinate : Item → Coordinate) (items : List Item) :
    Computability.boolStableSort
        (fun first second => decide (coordinate first ≤ coordinate second))
        items =
      StableListRanks.valuesByStableLowerRank coordinate items := by
  let coordinateRelation : (Item × Nat) → (Item × Nat) → Prop :=
    fun first second =>
      StableListRanks.indexedCoordinate coordinate first ≤
        StableListRanks.indexedCoordinate coordinate second
  unfold Computability.boolStableSort
    StableListRanks.valuesByStableLowerRank
  rw [Computability.boolInsertionSort_eq_insertionSort
    (List.zipIdxLE fun first second =>
      decide (coordinate first ≤ coordinate second))
    coordinateRelation]
  · rw [StrictListRanks.valuesByLowerRank_eq_insertionSort_of_coordinate_nodup
      (StableListRanks.indexedCoordinate coordinate) items.zipIdx
      (StableListRanks.indexedCoordinate_zipIdx_nodup coordinate items)]
  · rintro ⟨first, firstIndex⟩ ⟨second, secondIndex⟩
    simp only [coordinateRelation]
    rw [show StableListRanks.indexedCoordinate coordinate
          (first, firstIndex) =
        toLex (coordinate first, firstIndex) by rfl]
    rw [show StableListRanks.indexedCoordinate coordinate
          (second, secondIndex) =
        toLex (coordinate second, secondIndex) by rfl]
    rw [Prod.Lex.toLex_le_toLex]
    by_cases forward : coordinate first ≤ coordinate second
    · by_cases reverse : coordinate second ≤ coordinate first
      · have equal : coordinate first = coordinate second :=
          le_antisymm forward reverse
        simp [List.zipIdxLE, equal]
      · have strict : coordinate first < coordinate second :=
          lt_of_le_of_ne forward fun equal => reverse equal.ge
        simp [List.zipIdxLE, forward, reverse, strict, strict.ne]
    · have strict : coordinate second < coordinate first :=
        lt_of_not_ge forward
      have notEqual : coordinate first ≠ coordinate second :=
        strict.ne.symm
      simp [List.zipIdxLE, forward, strict.le, notEqual]

namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- For every retained occurrence fiber, geometric merge sorting is exactly
stable sorting by the numeric `(direction rank, radial length)` key. -/
theorem angularOccurrenceVariables_eq_valuesByStableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (atom : Variable) :
    angularOccurrenceVariables source routes atom =
      StableListRanks.valuesByStableLowerRank
        (retainedOccurrenceTerminalCoordinate routes)
        (occurrenceVariables source atom) := by
  let items := occurrenceVariables source atom
  let coordinate : ThreeOccurrenceVariable Variable → Nat ×ₗ Nat :=
    retainedOccurrenceTerminalCoordinate (Variable := Variable) routes
  let coordinateLE :
      ThreeOccurrenceVariable Variable →
        ThreeOccurrenceVariable Variable → Bool :=
    fun first second => decide (coordinate first ≤ coordinate second)
  have agree : ∀ first ∈ items, ∀ second ∈ items,
      occurrenceAngleLE routes first second =
        coordinateLE first second := by
    intro first firstMember second secondMember
    exact occurrenceAngleLE_eq_decide_terminalCoordinateLE
      routes first second
      (certificate atom first firstMember)
      (certificate atom second secondMember)
  unfold angularOccurrenceVariables
  change items.mergeSort (occurrenceAngleLE routes) = _
  calc
    _ = Computability.boolStableSort
          (occurrenceAngleLE routes) items :=
      (Computability.boolStableSort_eq_mergeSort
        (occurrenceAngleLE routes)
        (occurrenceAngleLE_transitive routes)
        (occurrenceAngleLE_total routes) items).symm
    _ = Computability.boolStableSort coordinateLE items :=
      boolStableSort_eq_of_eq_on
        (occurrenceAngleLE routes) coordinateLE items agree
    _ = StableListRanks.valuesByStableLowerRank coordinate items :=
      boolStableSort_decideLE_eq_valuesByStableLowerRank
        coordinate items

end PeriodicEightOccurrenceSplit
end LeanTrominoes

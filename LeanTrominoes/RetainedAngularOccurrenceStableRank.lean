/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceStableSort
import LeanTrominoes.StableListIndexedLowerRankSemantics
import LeanTrominoes.StableListSelectedRankEnumerationSemantics

/-! # Stable numeric ranks of retained angular occurrences -/

namespace LeanTrominoes
namespace StableListRanks

/-- In a duplicate-free presentation, the stable indexed lower rank of a
value at its presentation index is exactly its index in the stable lower-rank
enumeration. -/
theorem selectedIndexedLowerRank_true_eq_idxOf_valuesByStableLowerRank
    {Value Coordinate : Type*}
    [DecidableEq Value] [BEq Value] [LawfulBEq Value]
    [LinearOrder Coordinate]
    (coordinate : Value → Coordinate)
    (values : List Value) (valuesNodup : values.Nodup)
    (value : Value) (valueMember : value ∈ values) :
    selectedIndexedLowerRank coordinate (fun _ => true) values
        (value, values.idxOf value) =
      (valuesByStableLowerRank coordinate values).idxOf value := by
  letI : BEq (Value × Nat) := instBEqOfDecidableEq
  let entry : Value × Nat := (value, values.idxOf value)
  let filtered := values.zipIdx.filter fun other => true
  let ranked := StrictListRanks.valuesByLowerRank
    (indexedCoordinate coordinate) filtered
  have entryMember : entry ∈ values.zipIdx := by
    exact List.mk_mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_idxOf valueMember)
  have rankEq :
      selectedIndexedLowerRank coordinate (fun _ => true) values entry =
        ranked.idxOf entry := by
    simpa [ranked, filtered] using
      (selectedIndexedLowerRank_eq_idxOf_rankEnumeration
        coordinate (fun _ => true) values entry entryMember (by rfl))
  have coordinateNodup :
      (filtered.map (indexedCoordinate coordinate)).Nodup := by
    exact (indexedCoordinate_zipIdx_nodup coordinate values).sublist
      (List.filter_sublist.map (indexedCoordinate coordinate))
  have filteredMember : entry ∈ filtered := by
    simp [filtered, entryMember]
  have rankedMember : entry ∈ ranked := by
    change entry ∈ StrictListRanks.valuesByLowerRank
      (indexedCoordinate coordinate) filtered
    rw [StrictListRanks.valuesByLowerRank_eq_insertionSort_of_coordinate_nodup
      (indexedCoordinate coordinate) filtered coordinateNodup]
    exact (List.mem_insertionSort
      (r := fun first second : Value × Nat =>
        indexedCoordinate coordinate first ≤
          indexedCoordinate coordinate second)).mpr filteredMember
  have projectedEq :
      ranked.map Prod.fst = valuesByStableLowerRank coordinate values := by
    simpa [ranked, filtered] using
      (selectedIndexedValuesByLowerRank_map_fst
        coordinate (fun _ : Value => true) values)
  have stableNodup :
      (valuesByStableLowerRank coordinate values).Nodup := by
    rw [valuesByStableLowerRank_eq_insertionSort]
    exact (List.perm_insertionSort
      (fun first second : Value => coordinate first ≤ coordinate second)
      values).nodup_iff.mpr valuesNodup
  have projectedNodup : (ranked.map Prod.fst).Nodup := by
    rw [projectedEq]
    exact stableNodup
  have rankLt : ranked.idxOf entry < ranked.length :=
    List.idxOf_lt_length_of_mem rankedMember
  have rankedAt : ranked[ranked.idxOf entry]'rankLt = entry :=
    List.getElem_idxOf rankLt
  have projectedLt :
      ranked.idxOf entry < (ranked.map Prod.fst).length := by
    simpa using rankLt
  have projectedAt :
      (ranked.map Prod.fst)[ranked.idxOf entry]'projectedLt = value := by
    simp only [List.getElem_map]
    rw [rankedAt]
  have projectedIndex :
      (ranked.map Prod.fst).idxOf value = ranked.idxOf entry := by
    rw [← projectedAt]
    exact projectedNodup.idxOf_getElem (ranked.idxOf entry) projectedLt
  change selectedIndexedLowerRank coordinate (fun _ => true) values entry = _
  calc
    _ = ranked.idxOf entry := rankEq
    _ = (ranked.map Prod.fst).idxOf value := projectedIndex.symm
    _ = (valuesByStableLowerRank coordinate values).idxOf value := by
      rw [projectedEq]

end StableListRanks

namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Stable numeric terminal rank of one named occurrence inside its source
atom's presentation fiber. -/
def retainedOccurrenceStableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable) : Nat :=
  let copies := occurrenceVariables source atom
  StableListRanks.selectedIndexedLowerRank
    (retainedOccurrenceTerminalCoordinate routes)
    (fun _ => true) copies (copy, copies.idxOf copy)

/-- For a genuine certified occurrence, its index in the geometric angular
fiber is exactly its stable numeric terminal rank. -/
theorem angularOccurrenceVariables_idxOf_eq_stableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (taggedMember :
      (literal, clauseIndex, literalIndex) ∈ taggedLiterals source) :
    (angularOccurrenceVariables source routes literal.atom).idxOf
        (literal.atom, clauseIndex, literalIndex) =
      retainedOccurrenceStableTerminalRank source routes literal.atom
        (literal.atom, clauseIndex, literalIndex) := by
  let copy : ThreeOccurrenceVariable Variable :=
    (literal.atom, clauseIndex, literalIndex)
  have copyMember : copy ∈ occurrenceVariables source literal.atom :=
    occurrenceVariables_mem source taggedMember
  unfold retainedOccurrenceStableTerminalRank
  change (angularOccurrenceVariables source routes literal.atom).idxOf copy = _
  rw [angularOccurrenceVariables_eq_valuesByStableTerminalRank
    source routes certificate literal.atom]
  exact
    (StableListRanks.selectedIndexedLowerRank_true_eq_idxOf_valuesByStableLowerRank
      (retainedOccurrenceTerminalCoordinate routes)
      (occurrenceVariables source literal.atom)
      (occurrenceVariables_nodup source literal.atom)
      copy copyMember).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes

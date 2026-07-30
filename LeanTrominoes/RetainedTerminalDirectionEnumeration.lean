import LeanTrominoes.RetainedTerminalDirections

/-!
# Finite enumeration of retained terminal directions

The annular Figure 7 adapter is a finite problem once radial lengths have
been separated from the direction vocabulary.  This file lists the eleven
retained directions in their exact east-first angular-rank order and proves
that the list is complete, duplicate-free, and rank-indexed.

Later executable geometry can therefore enumerate lists over this catalog
instead of repeatedly splitting the two constructors of
`RetainedTerminalDirection`.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

/-- All retained terminal directions, in increasing angular-rank order. -/
def retainedTerminalDirections :
    List RetainedTerminalDirection :=
  [.compass .east,
    .routedClause .left,
    .compass .southeast,
    .compass .south,
    .routedClause .right,
    .compass .southwest,
    .compass .west,
    .compass .northwest,
    .compass .north,
    .compass .northeast,
    .routedClause .middle]

@[simp]
theorem retainedTerminalDirections_length :
    retainedTerminalDirections.length = 11 := by
  rfl

/-- The finite direction catalog contains no duplicate direction. -/
theorem retainedTerminalDirections_nodup :
    retainedTerminalDirections.Nodup := by
  native_decide

/-- Every retained terminal direction occurs in the finite catalog. -/
theorem mem_retainedTerminalDirections
    (direction : RetainedTerminalDirection) :
    direction ∈ retainedTerminalDirections := by
  cases direction with
  | compass port =>
      cases port <;>
        simp [retainedTerminalDirections]
  | routedClause arm =>
      cases arm <;>
        simp [retainedTerminalDirections]

/-- Mapping the catalog to angular ranks produces exactly `0, …, 10`. -/
@[simp]
theorem retainedTerminalDirections_map_angularRank :
    retainedTerminalDirections.map
        RetainedTerminalDirection.angularRank =
      List.range 11 := by
  native_decide

/-- Angular rank uniquely identifies a retained terminal direction. -/
theorem RetainedTerminalDirection.angularRank_injective :
    Function.Injective
      RetainedTerminalDirection.angularRank := by
  intro first second equal
  cases first with
  | compass firstPort =>
      cases firstPort <;>
        cases second with
        | compass secondPort =>
            cases secondPort <;>
              simp [RetainedTerminalDirection.angularRank]
                at equal ⊢
        | routedClause secondArm =>
            cases secondArm <;>
              simp [RetainedTerminalDirection.angularRank]
                at equal
  | routedClause firstArm =>
      cases firstArm <;>
        cases second with
        | compass secondPort =>
            cases secondPort <;>
              simp [RetainedTerminalDirection.angularRank]
                at equal
        | routedClause secondArm =>
            cases secondArm <;>
              simp [RetainedTerminalDirection.angularRank]
                at equal ⊢

/-- Two catalog entries are ordered exactly when their list indices are
ordered. -/
theorem retainedTerminalDirections_getElem_rank_le_iff
    (first second : Nat)
    (firstLt : first < retainedTerminalDirections.length)
    (secondLt : second < retainedTerminalDirections.length) :
    (retainedTerminalDirections[first]'firstLt).angularRank ≤
        (retainedTerminalDirections[second]'secondLt).angularRank ↔
      first ≤ second := by
  simp only [retainedTerminalDirections_length] at firstLt secondLt
  have firstLe : first ≤ 10 := by
    omega
  have secondLe : second ≤ 10 := by
    omega
  interval_cases first <;>
    interval_cases second <;>
      simp [retainedTerminalDirections,
        RetainedTerminalDirection.angularRank]

/-- In particular, the angular rank of a catalog entry is its index. -/
@[simp]
theorem retainedTerminalDirections_getElem_angularRank
    (index : Nat)
    (indexLt : index < retainedTerminalDirections.length) :
    (retainedTerminalDirections[index]'indexLt).angularRank =
      index := by
  simp only [retainedTerminalDirections_length] at indexLt
  have indexLe : index ≤ 10 := by
    omega
  interval_cases index <;>
    simp [retainedTerminalDirections,
      RetainedTerminalDirection.angularRank]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

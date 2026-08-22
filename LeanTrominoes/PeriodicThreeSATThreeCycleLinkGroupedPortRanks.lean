/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkGroupedTargetIndices

/-! # Prefix ranks in duplicate-free occurrence cycles -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

def linkAtoms {Value : Type*} : List (Value × Value) → List Value
  | [] => []
  | link :: links => link.1 :: link.2 :: linkAtoms links

def cycleLinkAtoms {Variable : Type*}
    (values : List (ThreeOccurrenceVariable Variable)) :
    List (ThreeOccurrenceVariable Variable) :=
  linkAtoms (cycleLinks values)

theorem linkAtoms_cycleLinksFrom
    {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    linkAtoms (cycleLinksFrom first current rest) =
      current :: (rest.flatMap fun value => [value, value]) ++ [first] := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest induction =>
      simp [linkAtoms, cycleLinksFrom, induction]

theorem cycleLinkAtoms_cons
    {Variable : Type*}
    (first : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    cycleLinkAtoms (first :: rest) =
      first :: (rest.flatMap fun value => [value, value]) ++ [first] := by
  exact linkAtoms_cycleLinksFrom first first rest

/-- Prefix multiplicity ranks, carrying the already scanned word. -/
def prefixRanksFrom {Value : Type*} [BEq Value] :
    List Value → List Value → List Nat
  | _, [] => []
  | seen, value :: values =>
      (1 + seen.count value) :: prefixRanksFrom (seen ++ [value]) values

def prefixRanks {Value : Type*} [BEq Value]
    (values : List Value) : List Nat :=
  prefixRanksFrom [] values

theorem prefixRanksFrom_duplicate_then_final
    {Value : Type*} [BEq Value] [LawfulBEq Value]
    (first : Value) (rest seen : List Value)
    (firstCount : seen.count first = 1)
    (restZero : ∀ value ∈ rest, seen.count value = 0)
    (restNodup : rest.Nodup) (firstNotRest : first ∉ rest) :
    prefixRanksFrom seen
        ((rest.flatMap fun value => [value, value]) ++ [first]) =
      (rest.flatMap fun _ => [1, 2]) ++ [2] := by
  induction rest generalizing seen with
  | nil =>
      simp [prefixRanksFrom, firstCount]
  | cons value rest induction =>
      have valueZero := restZero value List.mem_cons_self
      have valueNotRest := (List.nodup_cons.mp restNodup).1
      have restNodup' := (List.nodup_cons.mp restNodup).2
      have valueNeFirst : value ≠ first := by
        intro equal
        exact firstNotRest (equal ▸ List.mem_cons_self)
      have firstNotRest' : first ∉ rest := by
        intro member
        exact firstNotRest (List.mem_cons_of_mem value member)
      let nextSeen := (seen ++ [value]) ++ [value]
      have nextFirstCount : nextSeen.count first = 1 := by
        simp [nextSeen, List.count_append, firstCount, valueNeFirst]
      have nextRestZero : ∀ later ∈ rest,
          nextSeen.count later = 0 := by
        intro later laterMember
        have laterZero := restZero later
          (List.mem_cons_of_mem value laterMember)
        have valueNeLater : value ≠ later := by
          intro equal
          exact valueNotRest (equal ▸ laterMember)
        simp [nextSeen, List.count_append, laterZero, valueNeLater]
      have tail := induction nextSeen nextFirstCount nextRestZero
        restNodup' firstNotRest'
      change prefixRanksFrom seen
          (value :: value ::
            ((rest.flatMap fun value => [value, value]) ++ [first])) =
        1 :: 2 :: (rest.flatMap fun _ => [1, 2]) ++ [2]
      simp only [prefixRanksFrom, valueZero, Nat.add_zero]
      change 1 :: (1 + (seen ++ [value]).count value) ::
          prefixRanksFrom nextSeen
            ((rest.flatMap fun value => [value, value]) ++ [first]) =
        1 :: 2 :: (rest.flatMap fun _ => [1, 2]) ++ [2]
      have once : (seen ++ [value]).count value = 1 := by
        simp [List.count_append, valueZero]
      rw [once, tail]
      rfl

theorem prefixRanks_cycleLinkAtoms_cons
    {Variable : Type*} [DecidableEq Variable]
    (first : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable))
    (nodup : (first :: rest).Nodup) :
    prefixRanks (cycleLinkAtoms (first :: rest)) =
      1 :: (rest.flatMap fun _ => [1, 2]) ++ [2] := by
  rw [cycleLinkAtoms_cons]
  unfold prefixRanks
  simp only [List.cons_append, prefixRanksFrom, List.count_nil,
    Nat.add_zero]
  have firstNotRest := (List.nodup_cons.mp nodup).1
  have restNodup := (List.nodup_cons.mp nodup).2
  have firstCount : ([first] :
      List (ThreeOccurrenceVariable Variable)).count first = 1 := by simp
  have restZero : ∀ value ∈ rest,
      ([first] : List (ThreeOccurrenceVariable Variable)).count value = 0 := by
    intro value valueMember
    have different : first ≠ value := by
      intro equal
      exact firstNotRest (equal ▸ valueMember)
    simp [different]
  simpa only [List.nil_append] using congrArg (fun ranks => 1 :: ranks)
    (prefixRanksFrom_duplicate_then_final first rest [first]
      firstCount restZero restNodup firstNotRest)

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes

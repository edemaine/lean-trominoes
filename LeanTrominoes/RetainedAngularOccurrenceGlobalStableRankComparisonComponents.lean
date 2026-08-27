/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankPipelineData

/-! # Component comparisons for global occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

variable {Variable : Type*} [DecidableEq Variable]

/-- Target-major ordered pairs of all source occurrences. -/
def retainedOccurrenceGlobalOrderedPairs
    (source : PeriodicCNF Variable) :
    List (ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable) :=
  let copies := allOccurrenceVariables source
  copies.flatMap fun target =>
    copies.map fun candidate => (target, candidate)

/-- Same-atom bit of every target/candidate occurrence pair. -/
def retainedOccurrenceGlobalAtomEqualityBits
    (source : PeriodicCNF Variable) : List Bool :=
  (retainedOccurrenceGlobalOrderedPairs source).map fun pair =>
    decide (pair.2.1 = pair.1.1)

/-- Strict terminal-coordinate comparison bit of every target/candidate
occurrence pair. -/
def retainedOccurrenceGlobalTerminalStrictLowerBits
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Bool :=
  (retainedOccurrenceGlobalOrderedPairs source).map fun pair =>
    decide
      (retainedOccurrenceTerminalCoordinate routes pair.2 <
        retainedOccurrenceTerminalCoordinate routes pair.1)

/-- Equal terminal-coordinate bit of every target/candidate occurrence pair. -/
def retainedOccurrenceGlobalTerminalEqualityBits
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Bool :=
  (retainedOccurrenceGlobalOrderedPairs source).map fun pair =>
    decide
      (retainedOccurrenceTerminalCoordinate routes pair.2 =
        retainedOccurrenceTerminalCoordinate routes pair.1)

@[simp] theorem retainedOccurrenceGlobalAtomEqualityBits_length
    (source : PeriodicCNF Variable) :
    (retainedOccurrenceGlobalAtomEqualityBits source).length =
      (retainedOccurrenceGlobalOrderedPairs source).length := by
  simp [retainedOccurrenceGlobalAtomEqualityBits]

omit [DecidableEq Variable] in
@[simp] theorem retainedOccurrenceGlobalTerminalStrictLowerBits_length
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalTerminalStrictLowerBits source routes).length =
      (retainedOccurrenceGlobalOrderedPairs source).length := by
  simp [retainedOccurrenceGlobalTerminalStrictLowerBits]

omit [DecidableEq Variable] in
@[simp] theorem retainedOccurrenceGlobalTerminalEqualityBits_length
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalTerminalEqualityBits source routes).length =
      (retainedOccurrenceGlobalOrderedPairs source).length := by
  simp [retainedOccurrenceGlobalTerminalEqualityBits]

private theorem zipWith_map_map
    {Value First Second Output : Type*}
    (operation : First → Second → Output)
    (values : List Value) (first : Value → First)
    (second : Value → Second) :
    List.zipWith operation (values.map first) (values.map second) =
      values.map fun value => operation (first value) (second value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, induction]

/-- Conjoining atom equality with strict terminal-coordinate order gives the
exact stable-rank strict-lower square. -/
theorem retainedOccurrenceGlobalStableLowerBits_eq_components
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableLowerBits source routes =
      List.zipWith (· && ·)
        (retainedOccurrenceGlobalAtomEqualityBits source)
        (retainedOccurrenceGlobalTerminalStrictLowerBits source routes) := by
  unfold retainedOccurrenceGlobalAtomEqualityBits
    retainedOccurrenceGlobalTerminalStrictLowerBits
  rw [zipWith_map_map]
  unfold retainedOccurrenceGlobalStableLowerBits
    retainedOccurrenceGlobalOrderedPairs
    retainedOccurrenceGlobalStableLowerPredicate
  dsimp only
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro target _targetMember
  rw [List.map_map]
  rfl

/-- Conjoining atom equality with terminal-coordinate equality gives the
exact stable-rank tie square. -/
theorem retainedOccurrenceGlobalStableTieBits_eq_components
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableTieBits source routes =
      List.zipWith (· && ·)
        (retainedOccurrenceGlobalAtomEqualityBits source)
        (retainedOccurrenceGlobalTerminalEqualityBits source routes) := by
  unfold retainedOccurrenceGlobalAtomEqualityBits
    retainedOccurrenceGlobalTerminalEqualityBits
  rw [zipWith_map_map]
  unfold retainedOccurrenceGlobalStableTieBits
    retainedOccurrenceGlobalOrderedPairs
    retainedOccurrenceGlobalStableTiePredicate
  dsimp only
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro target _targetMember
  rw [List.map_map]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes

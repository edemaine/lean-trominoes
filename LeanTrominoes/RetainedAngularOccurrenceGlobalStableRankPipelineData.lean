/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsEncoding
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankCountData
import LeanTrominoes.UnaryAlignedAddValidity

/-! # Pipeline data for global retained occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

variable {Variable : Type*} [DecidableEq Variable]

private theorem flatMap_map_length
    {First Second Output : Type*}
    (firsts : List First) (seconds : List Second)
    (output : First → Second → Output) :
    (firsts.flatMap fun first => seconds.map (output first)).length =
      firsts.length * seconds.length := by
  induction firsts with
  | nil => simp
  | cons first firsts induction =>
      simp [induction, Nat.succ_mul, Nat.add_comm]

/-- Side length of the global occurrence comparison squares. -/
def retainedOccurrenceGlobalStableRankSide
    (source : PeriodicCNF Variable) : Nat :=
  (allOccurrenceVariables source).length

/-- Flattened target-major strict-lower comparison square. -/
def retainedOccurrenceGlobalStableLowerBits
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Bool :=
  let copies := allOccurrenceVariables source
  copies.flatMap fun target =>
    copies.map (retainedOccurrenceGlobalStableLowerPredicate routes target)

/-- Flattened target-major equal-coordinate comparison square. -/
def retainedOccurrenceGlobalStableTieBits
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Bool :=
  let copies := allOccurrenceVariables source
  copies.flatMap fun target =>
    copies.map (retainedOccurrenceGlobalStableTiePredicate routes target)

@[simp] theorem retainedOccurrenceGlobalStableLowerBits_length
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableLowerBits source routes).length =
      retainedOccurrenceGlobalStableRankSide source ^ 2 := by
  unfold retainedOccurrenceGlobalStableLowerBits
    retainedOccurrenceGlobalStableRankSide
  dsimp only
  rw [flatMap_map_length]
  simp [pow_two]

@[simp] theorem retainedOccurrenceGlobalStableTieBits_length
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTieBits source routes).length =
      retainedOccurrenceGlobalStableRankSide source ^ 2 := by
  unfold retainedOccurrenceGlobalStableTieBits
    retainedOccurrenceGlobalStableRankSide
  dsimp only
  rw [flatMap_map_length]
  simp [pow_two]

/-- Promised Boolean square for strict-lower comparisons. -/
def retainedOccurrenceGlobalStableLowerSquareInput
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    BoolSquareRows.Input where
  bits := retainedOccurrenceGlobalStableLowerBits source routes
  square := by
    rw [retainedOccurrenceGlobalStableLowerBits_length, Nat.sqrt_eq']

/-- Promised Boolean square for equal-coordinate comparisons. -/
def retainedOccurrenceGlobalStableTieSquareInput
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    BoolSquareRows.Input where
  bits := retainedOccurrenceGlobalStableTieBits source routes
  square := by
    rw [retainedOccurrenceGlobalStableTieBits_length, Nat.sqrt_eq']

@[simp] theorem retainedOccurrenceGlobalStableLowerSquareInput_side
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableLowerSquareInput source routes).side =
      retainedOccurrenceGlobalStableRankSide source := by
  unfold BoolSquareRows.Input.side
    retainedOccurrenceGlobalStableLowerSquareInput
  rw [retainedOccurrenceGlobalStableLowerBits_length, Nat.sqrt_eq']

@[simp] theorem retainedOccurrenceGlobalStableTieSquareInput_side
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTieSquareInput source routes).side =
      retainedOccurrenceGlobalStableRankSide source := by
  unfold BoolSquareRows.Input.side
    retainedOccurrenceGlobalStableTieSquareInput
  rw [retainedOccurrenceGlobalStableTieBits_length, Nat.sqrt_eq']

/-- Delimited strict-lower rows recovered by the square reshaper. -/
def retainedOccurrenceGlobalStableLowerDelimitedRows
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    DelimitedBinaryWords.Input :=
  (retainedOccurrenceGlobalStableLowerSquareInput source routes).delimitedRows

/-- Delimited equal-coordinate rows recovered by the square reshaper. -/
def retainedOccurrenceGlobalStableTieDelimitedRows
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    DelimitedBinaryWords.Input :=
  (retainedOccurrenceGlobalStableTieSquareInput source routes).delimitedRows

/-- True count of every strict-lower row. -/
def retainedOccurrenceGlobalStableLowerCounts
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (retainedOccurrenceGlobalStableLowerDelimitedRows source routes)

/-- Successively longer prefix-true count of every equal-coordinate row. -/
def retainedOccurrenceGlobalStableTieCounts
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Nat :=
  DelimitedBinaryWordPrefixTrueCounts.counts
    (retainedOccurrenceGlobalStableTieDelimitedRows source routes)

@[simp] theorem retainedOccurrenceGlobalStableLowerCounts_length
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableLowerCounts source routes).length =
      retainedOccurrenceGlobalStableRankSide source := by
  unfold retainedOccurrenceGlobalStableLowerCounts
    retainedOccurrenceGlobalStableLowerDelimitedRows
    DelimitedBinaryWordTrueCounts.counts
    BoolSquareRows.Input.delimitedRows
  rw [List.length_map, BoolSquareRows.rows_length,
    retainedOccurrenceGlobalStableLowerSquareInput_side]

@[simp] theorem retainedOccurrenceGlobalStableTieCounts_length
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTieCounts source routes).length =
      retainedOccurrenceGlobalStableRankSide source := by
  unfold retainedOccurrenceGlobalStableTieCounts
    retainedOccurrenceGlobalStableTieDelimitedRows
    BoolSquareRows.Input.delimitedRows
  rw [DelimitedBinaryWordPrefixTrueCounts.counts_length,
    BoolSquareRows.rows_length,
    retainedOccurrenceGlobalStableTieSquareInput_side]

/-- Unary-add input for the strict-lower and earlier-tie counts. -/
def retainedOccurrenceGlobalStableRankAdditionInput
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    UnaryAlignedAddMachine.Input where
  firsts := retainedOccurrenceGlobalStableLowerCounts source routes
  seconds := retainedOccurrenceGlobalStableTieCounts source routes
  valid := UnaryAlignedAddMachine.Valid.of_length_eq (by simp)

/-- Complete square-count pipeline output. -/
def retainedOccurrenceGlobalStableRankPipeline
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Nat :=
  UnaryAlignedAddMachine.sums
    (retainedOccurrenceGlobalStableLowerCounts source routes)
    (retainedOccurrenceGlobalStableTieCounts source routes)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

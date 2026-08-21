/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration

/-! # Lengths of fixed canonical retained variable blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- There are exactly two canonical terminal variables per indexed drawing
segment. -/
@[simp] theorem retainedPeriodicTerminalVariables_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicTerminalVariables formula).length =
      2 * (drawing formula.incidenceGraph).indexedSegments.length := by
  simp [retainedPeriodicTerminalVariables, List.length_flatMap,
    Nat.mul_comm]

/-- There are exactly four canonical boundary variables per oriented
crossing. -/
@[simp] theorem retainedPeriodicBoundaryVariables_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicBoundaryVariables formula).length =
      4 * (orientedCrossings formula.incidenceGraph).length := by
  simp [retainedPeriodicBoundaryVariables, drawingCrossingBoundaries,
    List.length_flatMap, Nat.mul_comm]

/-- The explicit list contains all nine crossover-internal names. -/
@[simp] theorem crossoverInternals_length : crossoverInternals.length = 9 := by
  rfl

/-- There are exactly nine canonical internal variables per oriented
crossing. -/
@[simp] theorem retainedPeriodicCrossoverInternalVariables_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicCrossoverInternalVariables formula).length =
      9 * (orientedCrossings formula.incidenceGraph).length := by
  simp [retainedPeriodicCrossoverInternalVariables,
    List.length_flatMap, Nat.mul_comm]

end LeanTrominoes.PeriodicOrthocrossing

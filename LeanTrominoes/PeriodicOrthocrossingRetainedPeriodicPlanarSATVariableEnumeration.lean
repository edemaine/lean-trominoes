/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions

/-! # Finite enumeration of valid retained periodic planar-SAT variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The two translation-zero periodic terminal variables on every indexed
drawing segment. -/
def retainedPeriodicTerminalVariables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicPlanarSATVariable Variable) :=
  ((drawing (PeriodicCNF.incidenceGraph formula)).indexedSegments).flatMap
    fun indexed =>
      [.terminal indexed .start, .terminal indexed .finish]

/-- The periodic boundary variable at every canonical drawing crossing. -/
def retainedPeriodicBoundaryVariables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicPlanarSATVariable Variable) :=
  (drawingCrossingBoundaries
      (PeriodicCNF.incidenceGraph formula)).map .boundary

/-- The periodic source atom at every represented translation-zero variable
route site. -/
def retainedPeriodicAtomVariables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicPlanarSATVariable Variable) :=
  ((drawingVariableRouteSites formula).filter fun site =>
      site.2 = (0, 0)).map fun site => .atom site.1

/-- All nine periodic internal variables at every canonical crossing. -/
def crossoverInternals : List CrossoverInternal :=
  [.aInnerLeft, .upperLeft, .lowerLeft, .bInnerTop, .center,
    .bInnerBottom, .upperRight, .lowerRight, .aInnerRight]

@[simp] theorem mem_crossoverInternals (internal : CrossoverInternal) :
    internal ∈ crossoverInternals := by
  cases internal <;> simp [crossoverInternals]

/-- All nine periodic internal variables at every canonical crossing. -/
def retainedPeriodicCrossoverInternalVariables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicPlanarSATVariable Variable) :=
  (orientedCrossings
      (PeriodicCNF.incidenceGraph formula)).flatMap fun crossing =>
    crossoverInternals.map fun internal =>
      .crossoverInternal (crossing, internal)

/-- Canonical finite enumeration of the four valid periodic routed-SAT
protovariable families. -/
def retainedDrawingPeriodicPlanarSATVariables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicPlanarSATVariable Variable) :=
  retainedPeriodicTerminalVariables formula ++
    retainedPeriodicBoundaryVariables formula ++
      retainedPeriodicAtomVariables formula ++
        retainedPeriodicCrossoverInternalVariables formula

@[simp] theorem mem_retainedPeriodicTerminalVariables_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    atom ∈ retainedPeriodicTerminalVariables formula ↔
      ∃ indexed ∈
          (drawing (PeriodicCNF.incidenceGraph formula)).indexedSegments,
        atom = .terminal indexed .start ∨
          atom = .terminal indexed .finish := by
  simp [retainedPeriodicTerminalVariables]

@[simp] theorem mem_retainedPeriodicBoundaryVariables_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    atom ∈ retainedPeriodicBoundaryVariables formula ↔
      ∃ boundary ∈ drawingCrossingBoundaries
          (PeriodicCNF.incidenceGraph formula),
        atom = .boundary boundary := by
  simp [retainedPeriodicBoundaryVariables, eq_comm]

@[simp] theorem mem_retainedPeriodicAtomVariables_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    atom ∈ retainedPeriodicAtomVariables formula ↔
      ∃ sourceAtom,
        (sourceAtom, (0, 0)) ∈ drawingVariableRouteSites formula ∧
          atom = .atom sourceAtom := by
  simp [retainedPeriodicAtomVariables, eq_comm]

@[simp] theorem mem_retainedPeriodicCrossoverInternalVariables_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    atom ∈ retainedPeriodicCrossoverInternalVariables formula ↔
      ∃ crossing ∈ orientedCrossings
          (PeriodicCNF.incidenceGraph formula),
        ∃ internal : CrossoverInternal,
          atom = .crossoverInternal (crossing, internal) := by
  simp [retainedPeriodicCrossoverInternalVariables, eq_comm]

/-- Membership in the canonical finite enumeration is exactly the geometric
validity predicate used by the retained periodic construction. -/
@[simp] theorem mem_retainedDrawingPeriodicPlanarSATVariables_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    atom ∈ retainedDrawingPeriodicPlanarSATVariables formula ↔
      RetainedDrawingPeriodicPlanarSATVariableValid formula atom := by
  cases atom with
  | terminal indexed endpoint =>
      cases endpoint <;>
        simp [retainedDrawingPeriodicPlanarSATVariables,
          RetainedDrawingPeriodicPlanarSATVariableValid]
  | boundary boundary =>
      simp [retainedDrawingPeriodicPlanarSATVariables,
        RetainedDrawingPeriodicPlanarSATVariableValid]
  | atom sourceAtom =>
      simp [retainedDrawingPeriodicPlanarSATVariables,
        RetainedDrawingPeriodicPlanarSATVariableValid]
  | crossoverInternal internal =>
      rcases internal with ⟨crossing, internal⟩
      simp [retainedDrawingPeriodicPlanarSATVariables,
        RetainedDrawingPeriodicPlanarSATVariableValid]

end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicTerminalVariableNodup
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicBoundaryVariableNodup
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicAtomVariableNodup
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicCrossoverInternalVariableNodup

/-! # Duplicate-free canonical retained variable enumeration -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The four constructor-distinct canonical blocks are each duplicate-free
and mutually disjoint, so their complete enumeration is duplicate-free. -/
theorem retainedDrawingPeriodicPlanarSATVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDrawingPeriodicPlanarSATVariables formula).Nodup := by
  let terminals := retainedPeriodicTerminalVariables formula
  let boundaries := retainedPeriodicBoundaryVariables formula
  let atoms := retainedPeriodicAtomVariables formula
  let internals := retainedPeriodicCrossoverInternalVariables formula
  have terminalBoundaryDisjoint :
      List.Disjoint terminals boundaries := by
    rw [List.disjoint_left]
    intro item terminalMem boundaryMem
    cases item <;> simp_all [terminals, boundaries]
  have terminalAtomDisjoint : List.Disjoint terminals atoms := by
    rw [List.disjoint_left]
    intro item terminalMem atomMem
    cases item <;> simp_all [terminals, atoms]
  have terminalInternalDisjoint :
      List.Disjoint terminals internals := by
    rw [List.disjoint_left]
    intro item terminalMem internalMem
    cases item <;> simp_all [terminals, internals]
  have boundaryAtomDisjoint : List.Disjoint boundaries atoms := by
    rw [List.disjoint_left]
    intro item boundaryMem atomMem
    cases item <;> simp_all [boundaries, atoms]
  have boundaryInternalDisjoint :
      List.Disjoint boundaries internals := by
    rw [List.disjoint_left]
    intro item boundaryMem internalMem
    cases item <;> simp_all [boundaries, internals]
  have atomInternalDisjoint : List.Disjoint atoms internals := by
    rw [List.disjoint_left]
    intro item atomMem internalMem
    cases item <;> simp_all [atoms, internals]
  have terminalBoundaryNodup : (terminals ++ boundaries).Nodup :=
    (retainedPeriodicTerminalVariables_nodup formula).append
      (retainedPeriodicBoundaryVariables_nodup formula)
      terminalBoundaryDisjoint
  have terminalBoundaryAtomNodup :
      (terminals ++ boundaries ++ atoms).Nodup :=
    terminalBoundaryNodup.append
      (retainedPeriodicAtomVariables_nodup formula) (by
        rw [List.disjoint_append_left]
        exact ⟨terminalAtomDisjoint, boundaryAtomDisjoint⟩)
  have allNodup :
      (terminals ++ boundaries ++ atoms ++ internals).Nodup :=
    terminalBoundaryAtomNodup.append
      (retainedPeriodicCrossoverInternalVariables_nodup formula) (by
        rw [List.disjoint_append_left,
          List.disjoint_append_left]
        exact
          ⟨⟨terminalInternalDisjoint, boundaryInternalDisjoint⟩,
            atomInternalDisjoint⟩)
  simpa [retainedDrawingPeriodicPlanarSATVariables,
    terminals, boundaries, atoms, internals] using allNodup

end LeanTrominoes.PeriodicOrthocrossing

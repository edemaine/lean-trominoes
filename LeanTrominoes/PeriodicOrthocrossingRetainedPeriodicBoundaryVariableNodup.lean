/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration

/-! # Duplicate-free canonical boundary variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The four boundary records at each canonical crossing are globally
duplicate-free. -/
theorem drawingCrossingBoundaries_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawingCrossingBoundaries graph).Nodup := by
  unfold drawingCrossingBoundaries
  rw [List.nodup_flatMap]
  constructor
  · intro crossing _
    simp
  · exact (orientedCrossings_nodup graph).imp fun
      {first second} different => by
        change List.Disjoint
          [CrossingBoundary.mk first .left,
            CrossingBoundary.mk first .right,
            CrossingBoundary.mk first .top,
            CrossingBoundary.mk first .bottom]
          [CrossingBoundary.mk second .left,
            CrossingBoundary.mk second .right,
            CrossingBoundary.mk second .top,
            CrossingBoundary.mk second .bottom]
        rw [List.disjoint_left]
        intro boundary firstMem secondMem
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at firstMem secondMem
        rcases firstMem with firstEq | firstEq | firstEq | firstEq <;>
          rcases secondMem with
            secondEq | secondEq | secondEq | secondEq
        all_goals
          exact different
            (CrossingBoundary.mk.inj
              (firstEq.symm.trans secondEq)).1

/-- The canonical boundary-variable block has no duplicates. -/
theorem retainedPeriodicBoundaryVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicBoundaryVariables formula).Nodup := by
  apply (drawingCrossingBoundaries_nodup
    (PeriodicCNF.incidenceGraph formula)).map
  intro first second equal
  exact PeriodicPlanarSATVariable.boundary.inj equal

end LeanTrominoes.PeriodicOrthocrossing

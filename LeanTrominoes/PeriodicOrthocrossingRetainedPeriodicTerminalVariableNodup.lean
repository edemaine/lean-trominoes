/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingIndexedSegmentsNodup
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration

/-! # Duplicate-free canonical terminal variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The translation-zero terminal block has no duplicate protovariables. -/
theorem retainedPeriodicTerminalVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicTerminalVariables formula).Nodup := by
  unfold retainedPeriodicTerminalVariables
  rw [List.nodup_flatMap]
  constructor
  · intro indexed _
    simp
  · exact
      (PeriodicGridDrawing.indexedSegments_nodup
        (drawing (PeriodicCNF.incidenceGraph formula))).imp fun
          {first second} different => by
            change List.Disjoint
              [PeriodicPlanarSATVariable.terminal first .start,
                .terminal first .finish]
              [PeriodicPlanarSATVariable.terminal second .start,
                .terminal second .finish]
            rw [List.disjoint_left]
            intro atom firstMem secondMem
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at firstMem secondMem
            rcases firstMem with firstEq | firstEq <;>
              rcases secondMem with secondEq | secondEq
            all_goals
              exact different
                (PeriodicPlanarSATVariable.terminal.inj
                  (firstEq.symm.trans secondEq)).1

end LeanTrominoes.PeriodicOrthocrossing

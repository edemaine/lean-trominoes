/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration

/-! # Duplicate-free canonical crossover-internal variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The fixed nine-name crossover-internal list has no duplicates. -/
theorem crossoverInternals_nodup : crossoverInternals.Nodup := by
  decide

/-- The canonical crossover-internal block has no duplicates. -/
theorem retainedPeriodicCrossoverInternalVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicCrossoverInternalVariables formula).Nodup := by
  unfold retainedPeriodicCrossoverInternalVariables
  rw [List.nodup_flatMap]
  constructor
  · intro crossing _
    apply crossoverInternals_nodup.map
    intro first second equal
    exact congrArg Prod.snd
      (PeriodicPlanarSATVariable.crossoverInternal.inj equal)
  · exact (orientedCrossings_nodup
      (PeriodicCNF.incidenceGraph formula)).imp fun
        {first second} different => by
          change List.Disjoint
            (crossoverInternals.map fun internal =>
              PeriodicPlanarSATVariable.crossoverInternal
                (first, internal))
            (crossoverInternals.map fun internal =>
              PeriodicPlanarSATVariable.crossoverInternal
                (second, internal))
          rw [List.disjoint_left]
          intro atom firstMem secondMem
          rcases List.mem_map.mp firstMem with
            ⟨firstInternal, _, firstEq⟩
          rcases List.mem_map.mp secondMem with
            ⟨secondInternal, _, secondEq⟩
          exact different
            (congrArg Prod.fst
              (PeriodicPlanarSATVariable.crossoverInternal.inj
                (firstEq.trans secondEq.symm)))

end LeanTrominoes.PeriodicOrthocrossing

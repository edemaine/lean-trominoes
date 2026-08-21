/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariableEnumeration

/-! # Duplicate-free canonical source-atom variables -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The represented translation-zero atom block has no duplicates. -/
theorem retainedPeriodicAtomVariables_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedPeriodicAtomVariables formula).Nodup := by
  unfold retainedPeriodicAtomVariables
  have allSitesNodup : (drawingVariableRouteSites formula).Nodup := by
    unfold drawingVariableRouteSites
    exact List.nodup_dedup _
  have zeroSitesNodup :
      ((drawingVariableRouteSites formula).filter fun site =>
        site.2 = (0, 0)).Nodup :=
    allSitesNodup.filter _
  apply zeroSitesNodup.map_on
  intro first firstMem second secondMem equal
  have atomEqual : first.1 = second.1 :=
    PeriodicPlanarSATVariable.atom.inj equal
  have firstZero : first.2 = (0, 0) := by
    simpa using (List.mem_filter.mp firstMem).2
  have secondZero : second.2 = (0, 0) := by
    simpa using (List.mem_filter.mp secondMem).2
  exact Prod.ext atomEqual (firstZero.trans secondZero.symm)

end LeanTrominoes.PeriodicOrthocrossing

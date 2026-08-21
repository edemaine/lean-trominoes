/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupLength
import LeanTrominoes.PeriodicCNFPlanarZeroVariableRouteSites
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicAtomVariableNodup

/-! # Exact canonical source-atom variable count -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- For a local incidence graph, the canonical translation-zero atom block
has exactly one member per distinct variable of the source formula. -/
theorem retainedPeriodicAtomVariables_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedPeriodicAtomVariables formula).length =
      formula.variableOccurrences.dedup.length := by
  let sourceAtoms : List (PeriodicPlanarSATVariable Variable) :=
    formula.variableOccurrences.dedup.map .atom
  have sourceAtomsNodup : sourceAtoms.Nodup := by
    apply (List.nodup_dedup formula.variableOccurrences).map
    intro first second equal
    exact PeriodicPlanarSATVariable.atom.inj equal
  have sameLength := List.dedup_length_eq_of_mem_iff
    (retainedPeriodicAtomVariables formula) sourceAtoms (by
      intro item
      cases item <;>
        simp [sourceAtoms,
          mem_variableOccurrences_iff_zeroSite_mem formula isLocal])
  simpa [List.dedup_eq_self.mpr
      (retainedPeriodicAtomVariables_nodup formula),
    List.dedup_eq_self.mpr sourceAtomsNodup,
    sourceAtoms] using sameLength

end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedGauge
import LeanTrominoes.PeriodicCNFPlanarThreeSATThree

/-!
# Vertical gauge of wrapped retained occurrences

Every variable that actually occurs after opaque wrapping comes from an
occurring retained planar-SAT variable.  Its geometric validity certificate
therefore makes the wrapped canonical gauge vertically zero.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every wrapped occurrence in the raw retained formula has zero vertical
canonical gauge. -/
theorem
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge_vertical_eq_zero_of_mem
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (horizontal : formula.incidenceGraph.HasZeroVerticalOffsets)
    {atom : WrappedPeriodicPlanarSATVariable Variable}
    (atomMember :
      atom ∈
        (wrapPeriodicPlanarSATFormula
          (retainedDrawingPeriodicPlanarSATFormula
            formula)).variableOccurrences) :
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
      formula atom).2 = 0 := by
  rw [wrapPeriodicPlanarSATFormula_variableOccurrences] at atomMember
  obtain ⟨rawAtom, rawAtomMember, rfl⟩ := List.mem_map.mp atomMember
  exact retainedDrawingWrappedPeriodicPlanarSATVariableGauge_vertical_eq_zero
    wellFormed isLocal horizontal rawAtom
    (retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_valid
      formula wellFormed degree isLocal rawAtomMember)

end PeriodicOrthocrossing
end LeanTrominoes

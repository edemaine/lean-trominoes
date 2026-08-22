/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarCrossoverNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-! # Canonical gauge of normalized crossover variables -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeCrossoverDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every boundary and internal variable of a canonical crossover already
lies in the fundamental physical period cell, so the retained canonical
variable gauge leaves it fixed. -/
theorem retainedGauge_normalizedCrossoverAtom_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (crossing : CrossingRecord)
    (crossingMember : crossing ∈ orientedCrossings formula.incidenceGraph)
    (role : CrossoverVariable) :
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula
      ⟨normalizedCrossoverAtom crossing role⟩ =
      (0, 0) := by
  unfold retainedDrawingWrappedPeriodicPlanarSATVariableGauge
  rw [wrappedDrawingPeriodicPlanarSATPlacement_canonicalPositionGauge_mk]
  have crossingOriented :
      crossing ∈ canonicalCrossings formula.incidenceGraph ∧
        (crossing.firstSegment formula.incidenceGraph).IsHorizontal :=
    (mem_orientedCrossings_iff formula.incidenceGraph crossing).mp
      crossingMember
  apply retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
    formula wellFormed
  · cases role <;>
      simp [normalizedCrossoverAtom,
        RetainedDrawingPeriodicPlanarSATVariableValid,
        drawingCrossingBoundaries, crossingMember, crossingOriented]
  · intro indexed endpoint equal
    cases role <;>
      simp [normalizedCrossoverAtom] at equal

end FormulaShapeCrossoverDirection
end PeriodicCNF
end LeanTrominoes

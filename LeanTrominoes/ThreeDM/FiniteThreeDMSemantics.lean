/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.FiniteRetainedThreeDMOffsets
import LeanTrominoes.ThreeDM.FiniteThreeDMContractionOffsets

/-! # Finite matching semantics of the retained planar 3DM target -/
namespace LeanTrominoes.PeriodicThreeDM

def FiniteSatisfies (problem : PeriodicThreeDM) (assignment : Nat → Bool) : Prop :=
  ∀ color atom,atom<problem.elementCount color →
    PeriodicOneInThree.ExactlyOne ((problem.incidences color atom).map
      (fun incidence => assignment incidence.tripleIndex))

def FiniteSatisfiable (problem : PeriodicThreeDM) : Prop :=
  ∃ assignment,problem.FiniteSatisfies assignment

theorem finiteSatisfiable_iff (problem : PeriodicThreeDM) (zero : problem.ZeroOffsets) :
    problem.FiniteSatisfiable ↔ problem.Satisfiable := by
  constructor
  · rintro ⟨assignment,holds⟩
    refine ⟨fun index _ => assignment index,?_⟩
    intro color atom bound cell
    exact holds color atom bound
  · rintro ⟨assignment,holds⟩
    refine ⟨fun index => assignment index (0,0),?_⟩
    intro color atom bound
    have atZero := holds color atom bound (0,0)
    have valuesEq : problem.incidentValues (problem.liftAssignment assignment) color atom (0,0) =
        (problem.incidences color atom).map (fun incidence => assignment incidence.tripleIndex (0,0)) := by
      apply List.map_congr_left
      intro incidence member
      simp [liftAssignment,incidence_offset_eq_zero zero color atom member,Cell.sub]
    rw [valuesEq] at atZero
    exact atZero
end LeanTrominoes.PeriodicThreeDM

namespace LeanTrominoes.PeriodicOrthocrossing
local instance {V : Type*} [DecidableEq V] :
    DecidableEq (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable V)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem retainedPlanarThreeDM_finite_satisfiable_iff
    {V : Type*} [DecidableEq V] (source : PeriodicCNF V)
    (sourceLocal : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) (nonempty : ∀ clause∈source.clauses,clause≠[])
    (zero : FiniteCNF.ZeroOffsets source) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem source
      sourceLocal width occurrences nonempty).FiniteSatisfiable ↔
      FiniteCNF.Satisfiable (FiniteCNF.erase source) := by
  rw [PeriodicThreeDM.finiteSatisfiable_iff _
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_zeroOffsets
      source sourceLocal width occurrences nonempty zero),
    retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_satisfiable_iff
      source sourceLocal width occurrences nonempty,
    FiniteCNF.satisfiable_erase source zero]
end LeanTrominoes.PeriodicOrthocrossing

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.FiniteThreeDMNormalization

/-! # A finite SAT-to-tromino region through the retained planar construction -/
noncomputable section
namespace LeanTrominoes.FiniteRetainedTrominoRegion
open PeriodicOrthocrossing Gadget
local instance {V : Type*} [DecidableEq V] :
    DecidableEq (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable V)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

variable {V : Type*} [DecidableEq V] (source : PeriodicCNF V)
    (sourceLocal : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) (nonempty : ∀ clause∈source.clauses,clause≠[])
    (zero : FiniteCNF.ZeroOffsets source)

def drawing : PeriodicOrthogonalDrawing :=
  (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
    source sourceLocal width occurrences nonempty).finiteNormalizedDrawing
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_zeroOffsets
      source sourceLocal width occurrences nonempty zero)
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
      source sourceLocal width occurrences nonempty)

def region (t : Tromino) : List Cell :=
  (drawing source sourceLocal width occurrences nonempty zero).expandedMotif t

/-- The finite motif is tileable precisely when the finite source CNF is satisfiable. -/
theorem correct (t : Tromino) :
    FiniteCNF.Satisfiable (FiniteCNF.erase source) ↔
      t.Tileable ((region source sourceLocal width occurrences nonempty zero t).toFinset : Set Cell) := by
  let presentation := retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
    source sourceLocal width occurrences nonempty
  have targetCorrect := presentation.finiteTrominoRegion_correct presentation.problemWellFormed
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
      source sourceLocal width occurrences nonempty)
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_zeroOffsets
      source sourceLocal width occurrences nonempty zero)
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
      source sourceLocal width occurrences nonempty)
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_separated
      source sourceLocal width occurrences nonempty)
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_routesSimple
      source sourceLocal width occurrences nonempty) t
  exact (retainedPlanarThreeDM_finite_satisfiable_iff
    source sourceLocal width occurrences nonempty zero).symm.trans targetCorrect
end LeanTrominoes.FiniteRetainedTrominoRegion

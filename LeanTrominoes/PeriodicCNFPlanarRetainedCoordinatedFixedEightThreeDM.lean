/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-!
# Coordinated retained fixed-eight 3DM endpoint

This module connects the coordinated retained unit-free exact-one formula
to the generic normalized periodic 3DM encoding.  It records all
nongeometric promises of the target.  Supplying the coordinated formula's
ribbon-ready planar incidence presentation is the remaining geometric
obligation before the normalized drawing assembly can be applied.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Variable type of the coordinated retained unit-free exact-one endpoint. -/
abbrev RetainedCoordinatedFixedEightOneInThreeVariable
    (Variable : Type*) :=
  OneInThreeNoUnitVariable
    (WrappedPeriodicVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable))

/-- Normalized periodic 3DM target of the coordinated retained exact-one
pipeline. -/
def retainedCoordinatedFixedEightPeriodicThreeDMProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source)
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
      source)

/-- The coordinated occurrence-three theorem, transferred to an explicitly
chosen decidable equality on the generated endpoint variables. -/
theorem
    retainedCoordinatedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
    {Variable : Type*} [DecidableEq Variable]
    (finalDecEq :
      DecidableEq
        (RetainedCoordinatedFixedEightOneInThreeVariable Variable))
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    @PeriodicCNF.OccurrencesAtMost
      (RetainedCoordinatedFixedEightOneInThreeVariable Variable)
      (@instBEqOfDecidableEq
        (RetainedCoordinatedFixedEightOneInThreeVariable Variable)
        finalDecEq)
      (by infer_instance) 3
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase := by
  have finalOccurrences :=
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase
      finalOccurrences

/-- Every triple reference in the coordinated normalized target names a
declared colored element. -/
theorem retainedCoordinatedFixedEightPeriodicThreeDMProblem_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPeriodicThreeDMProblem source).IsWellFormed := by
  unfold retainedCoordinatedFixedEightPeriodicThreeDMProblem
  exact
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_isWellFormed
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)

/-- Every colored element of the coordinated normalized target has degree
two or three. -/
theorem retainedCoordinatedFixedEightPeriodicThreeDMProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicThreeDMProblem
      source).DegreeTwoOrThree := by
  let finalDecEq :
      DecidableEq
        (RetainedCoordinatedFixedEightOneInThreeVariable Variable) :=
    inferInstance
  have finalOccurrences' :=
    retainedCoordinatedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
      finalDecEq source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold retainedCoordinatedFixedEightPeriodicThreeDMProblem
  exact
    @PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_degreeTwoOrThree
      (RetainedCoordinatedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      finalOccurrences'
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source)

/-- The coordinated normalized 3DM target has a perfect matching exactly
when the original periodic CNF is satisfiable. -/
theorem retainedCoordinatedFixedEightPeriodicThreeDMProblem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicThreeDMProblem source).Satisfiable ↔
      source.Satisfiable := by
  let finalDecEq :
      DecidableEq
        (RetainedCoordinatedFixedEightOneInThreeVariable Variable) :=
    inferInstance
  have finalOccurrences' :=
    retainedCoordinatedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
      finalDecEq source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold retainedCoordinatedFixedEightPeriodicThreeDMProblem
  exact
    (@PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_satisfiable_iff_source
      (RetainedCoordinatedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source)
      finalOccurrences'
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source)).trans
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences)

/-- The abstract incidence graph of the coordinated normalized 3DM target
admits the required orientation exactly when the original periodic CNF is
satisfiable. -/
theorem
    retainedCoordinatedFixedEightPeriodicThreeDMProblem_graphHasOrientation_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedCoordinatedFixedEightPeriodicThreeDMProblem
        source).GraphHasOrientation ↔
      source.Satisfiable := by
  exact
    (PeriodicThreeDM.satisfiable_iff_graphHasOrientation
      (retainedCoordinatedFixedEightPeriodicThreeDMProblem source)).symm.trans
      (retainedCoordinatedFixedEightPeriodicThreeDMProblem_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreePositioned
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-!
# Retained fixed-eight 3DM endpoint

This module connects the retained fixed-eight, unit-free exact-one formula to
the generic normalized periodic 3DM encoding.  It names the resulting 3DM
problem and records all of its nongeometric promises: well-formedness, colored
degree two or three, and equivalence of both perfect matchings and abstract
incidence orientations with satisfiability of the original periodic CNF.

The remaining work is geometric.  A continuously planar retained exact-one
presentation must still be supplied before the generic 3DM drawing assembly
can realize this semantic target.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Variable type of the retained unit-free exact-one endpoint. -/
abbrev RetainedFixedEightOneInThreeVariable (Variable : Type*) :=
  OneInThreeNoUnitVariable
    (WrappedPeriodicVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable))

/-- Normalized periodic 3DM target of the retained fixed-eight exact-one
pipeline. -/
def retainedFixedEightPeriodicThreeDMProblem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicThreeDM :=
  PeriodicPlanarOneInThreeToThreeDM.normalizedProblem
    (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
      source)
    (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source)

/-- The retained occurrence-three theorem, transferred to an explicitly
chosen decidable equality on the generated endpoint variables. -/
theorem
    retainedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
    {Variable : Type*} [DecidableEq Variable]
    (finalDecEq :
      DecidableEq (RetainedFixedEightOneInThreeVariable Variable))
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    @PeriodicCNF.OccurrencesAtMost
      (RetainedFixedEightOneInThreeVariable Variable)
      (@instBEqOfDecidableEq
        (RetainedFixedEightOneInThreeVariable Variable)
        finalDecEq)
      (by infer_instance) 3
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase := by
  have finalOccurrences :=
    retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_occurrencesAtMostThree
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source).erase
      finalOccurrences

/-- Every triple reference in the retained normalized target names a declared
colored element. -/
theorem retainedFixedEightPeriodicThreeDMProblem_isWellFormed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedFixedEightPeriodicThreeDMProblem source).IsWellFormed := by
  unfold retainedFixedEightPeriodicThreeDMProblem
  exact
    PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_isWellFormed
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source)

/-- Every colored element of the retained normalized target has degree two or
three. -/
theorem retainedFixedEightPeriodicThreeDMProblem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedFixedEightPeriodicThreeDMProblem source).DegreeTwoOrThree := by
  let finalDecEq :
      DecidableEq (RetainedFixedEightOneInThreeVariable Variable) :=
    inferInstance
  have finalOccurrences' :=
    retainedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
      finalDecEq source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold retainedFixedEightPeriodicThreeDMProblem
  exact
    @PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_degreeTwoOrThree
      (RetainedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source)
      finalOccurrences'
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source)

/-- The retained normalized 3DM target has a perfect matching exactly when
the original periodic CNF is satisfiable. -/
theorem retainedFixedEightPeriodicThreeDMProblem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedFixedEightPeriodicThreeDMProblem source).Satisfiable ↔
      source.Satisfiable := by
  let finalDecEq :
      DecidableEq (RetainedFixedEightOneInThreeVariable Variable) :=
    inferInstance
  have finalOccurrences' :=
    retainedFixedEightPeriodicOneInThreeNoUnits_occurrencesAtMostThreeFor
      finalDecEq source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  unfold retainedFixedEightPeriodicThreeDMProblem
  exact
    (@PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_satisfiable_iff_source
      (RetainedFixedEightOneInThreeVariable Variable)
      finalDecEq
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source)
      finalOccurrences'
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_arityTwoOrThree
        source)).trans
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences)

/-- The abstract incidence graph of the retained normalized 3DM target admits
the required orientation exactly when the original periodic CNF is
satisfiable. -/
theorem retainedFixedEightPeriodicThreeDMProblem_graphHasOrientation_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedFixedEightPeriodicThreeDMProblem source).GraphHasOrientation ↔
      source.Satisfiable := by
  exact
    (PeriodicThreeDM.satisfiable_iff_graphHasOrientation
      (retainedFixedEightPeriodicThreeDMProblem source)).symm.trans
      (retainedFixedEightPeriodicThreeDMProblem_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes

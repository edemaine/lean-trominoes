import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDM
import LeanTrominoes.PeriodicThreeDMContractionContinuousPlanarity

/-!
# Contracted drawing of the final planar 3DM endpoint

Degree-two colored vertices are suppressed before compiling the planar graph
to the normalized cell alphabet used by the tromino gadgets.  The generic
contraction layer already proves semantic preservation and transports the
complete geometric certificate; this module specializes those results to the
concrete retained Figure 9 endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The executable colored periodic graph obtained by suppressing every
degree-two element of the final 3DM instance. -/
noncomputable def retainedOrderedFixedEightFinalGaugedContractedGraph
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :=
  (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
    source sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty).contractedGraph

/-- The corresponding contracted drawing, obtained by retaining degree-three
incidences and joining the two routes through every suppressed element. -/
noncomputable def retainedOrderedFixedEightFinalGaugedContractedDrawing
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicGridDrawing :=
  (retainedOrderedFixedEightFinalGaugedPaddedContinuousPlanarPresentation
    source sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty).contractedDrawing

/-- The concrete contracted drawing is compatible with the executable
contracted graph. -/
theorem retainedOrderedFixedEightFinalGaugedContractedDrawing_isCompatible
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedContractedDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsCompatible
        (retainedOrderedFixedEightFinalGaugedContractedGraph
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty) := by
  exact
    (retainedOrderedFixedEightFinalGaugedPaddedContinuousPlanarPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).toPlanarPresentation
      |>.contractedDrawing_isCompatible

/-- Degree-two contraction preserves rectilinearity of every concrete
route. -/
theorem retainedOrderedFixedEightFinalGaugedContractedDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedContractedDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsOrthogonal := by
  exact
    (retainedOrderedFixedEightFinalGaugedPaddedContinuousPlanarPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).toPlanarPresentation
      |>.contractedDrawing_isOrthogonal

/-- Degree-two contraction also preserves exact continuous separation of all
lifted route-segment occurrences. -/
theorem
    retainedOrderedFixedEightFinalGaugedContractedDrawing_isContinuouslyPlanar
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedContractedDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsContinuouslyPlanar := by
  exact
    (retainedOrderedFixedEightFinalGaugedPaddedContinuousPlanarPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).contractedDrawing_isContinuouslyPlanar
        (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)

/-- The original local periodic CNF is satisfiable exactly when the final
contracted graph admits its trichromatic/monochromatic suppressed
orientation. -/
theorem retainedOrderedFixedEightFinalGauged_hasSuppressedOrientation_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).HasSuppressedOrientation ↔ source.Satisfiable := by
  exact
    (PeriodicThreeDM.satisfiable_iff_hasSuppressedOrientation
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).symm.trans
      (retainedOrderedFixedEightFinalGaugedPaddedPeriodicThreeDMProblem_satisfiable_iff
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes

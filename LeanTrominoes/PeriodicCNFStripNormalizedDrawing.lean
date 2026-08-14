/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalProblem
import LeanTrominoes.PeriodicThreeDMNormalizationStripBlankBoundary
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationEquivalence
import LeanTrominoes.PeriodicThreeDMNormalizationStripVertexSeparation

/-!
# Concrete normalized strip drawing for local periodic CNF
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- The actual rectangular normalized drawing used by the strip reduction. -/
def stripDrawing (source : PeriodicCNF Nat) : PeriodicOrthogonalDrawing :=
  (presentation source).toPlanarPresentation.stripNormalizedOrthogonalDrawing

/-- The concrete rectangular normalized drawing is well formed. -/
theorem stripDrawing_isWellFormed (source : PeriodicCNF Nat) :
    (stripDrawing source).IsWellFormed := by
  exact (presentation source).stripNormalizedOrthogonalDrawing_isWellFormed
    (presentation source).problemWellFormed
    (problem_degreeTwoOrThree source)
    (problem_isOneDimensional source)
    (presentation_routePointsInExpandedVerticalBand source)
    (presentation_separated source)
    (presentation_routesSimple source)

/-- Degree-three vertices remain separated in the rectangular drawing. -/
theorem stripDrawing_verticesSeparated (source : PeriodicCNF Nat) :
    (stripDrawing source).VerticesSeparated := by
  exact (presentation source).toPlanarPresentation
    |>.stripNormalizedOrthogonalDrawing_verticesSeparated

/-- The artificial vertical seam of the rectangular drawing is blank. -/
theorem stripDrawing_hasBlankVerticalBoundary (source : PeriodicCNF Nat) :
    (stripDrawing source).HasBlankVerticalBoundary := by
  exact
    (presentation source).stripNormalizedOrthogonalDrawing_hasBlankVerticalBoundary
      (presentation source).problemWellFormed
      (problem_degreeTwoOrThree source)
      (problem_isOneDimensional source)
      (presentation_routePointsInExpandedVerticalBand source)

/-- Exact semantics of the guarded source-to-rectangular-drawing pipeline. -/
theorem stripDrawing_correct (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      (stripDrawing source).HasOrientation := by
  exact (problem_correct source).trans
    ((presentation source)
      |>.stripNormalizedOrthogonalDrawing_hasOrientation_iff_satisfiable
        (presentation source).problemWellFormed
        (problem_degreeTwoOrThree source)
        (problem_isOneDimensional source)
        (presentation_routePointsInExpandedVerticalBand source)
        (presentation_separated source)
        (presentation_routesSimple source)).symm

end PeriodicCNFStripReduction
end LeanTrominoes

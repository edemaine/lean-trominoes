/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDM
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationOrientationEquivalence
import LeanTrominoes.PeriodicThreeDMNormalizationVertexSeparation
import LeanTrominoes.PeriodicThreeDMNormalizationWellFormed

/-!
# Semantic planar drawing endpoint for 1D periodic CNF

The guarded 3SAT-3 source is fed through the already verified retained planar
SAT, exact-one, polarity-normalization, planar 3DM, and orthogonal-normalization
pipeline.  This module packages the resulting concrete drawing and proves its
well-formedness, vertex separation, and exact source semantics.  Polynomial
time and the vertical blank-boundary property remain separate obligations.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

local instance sourceVariableDecidableEq : DecidableEq Variable :=
  Classical.decEq _

/-- The planar periodic 3DM problem generated from the guarded 3SAT-3
formula. -/
def problem (source : PeriodicCNF Nat) : PeriodicThreeDM :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

/-- The proof-backed continuously planar presentation of the generated
problem. -/
def presentation (source : PeriodicCNF Nat) :
    (problem source).ContinuousPlanarPresentation :=
  PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

/-- Runtime data consumed by the orthogonal normalization compiler. -/
def normalizationInput (source : PeriodicCNF Nat) :
    PeriodicThreeDM.NormalizationCompiler.Input :=
  PeriodicThreeDM.NormalizationCompiler.inputOfPresentation
    (presentation source).toPlanarPresentation

/-- The normalized orthogonal drawing used by the tromino strip gadgets. -/
def drawing (source : PeriodicCNF Nat) : PeriodicOrthogonalDrawing :=
  PeriodicThreeDM.NormalizationCompiler.compile (normalizationInput source)

@[simp] theorem normalizationInput_problem (source : PeriodicCNF Nat) :
    (normalizationInput source).problem = problem source := rfl

@[simp] theorem normalizationInput_drawing (source : PeriodicCNF Nat) :
    (normalizationInput source).drawing = (presentation source).drawing := rfl

theorem drawing_eq_normalizedOrthogonalDrawing
    (source : PeriodicCNF Nat) :
    drawing source =
      (presentation source).toPlanarPresentation.normalizedOrthogonalDrawing := by
  exact PeriodicThreeDM.NormalizationCompiler.compile_inputOfPresentation
    (presentation source).toPlanarPresentation

/-- Every generated colored 3DM element has degree two or three. -/
theorem problem_degreeTwoOrThree (source : PeriodicCNF Nat) :
    (problem source).DegreeTwoOrThree := by
  exact PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

/-- Distinct lifted routes of the generated planar drawing are disjoint. -/
theorem presentation_separated (source : PeriodicCNF Nat) :
    (presentation source).drawing.LiftedRoutesAvoidEachOther := by
  exact PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_separated
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

/-- Every stored route in the generated presentation is simple. -/
theorem presentation_routesSimple (source : PeriodicCNF Nat) :
    ∀ route ∈ (presentation source).drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  exact PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_routesSimple
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

/-- The guarded planar 3DM problem is satisfiable exactly on source
yes-instances. -/
theorem problem_correct (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      (problem source).Satisfiable := by
  exact (sourceFormula_correct source).trans
    (PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_satisfiable_iff
        (sourceFormula source)
        (sourceFormula_isLocal source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
        (sourceFormula_clausesNonempty source)).symm

/-- The normalized output drawing is well formed. -/
theorem drawing_isWellFormed (source : PeriodicCNF Nat) :
    (drawing source).IsWellFormed := by
  rw [drawing_eq_normalizedOrthogonalDrawing]
  exact (presentation source).normalizedOrthogonalDrawing_isWellFormed
    (presentation source).problemWellFormed
    (problem_degreeTwoOrThree source)
    (presentation_separated source)
    (presentation_routesSimple source)

/-- Degree-three vertices remain separated in the normalized drawing. -/
theorem drawing_verticesSeparated (source : PeriodicCNF Nat) :
    (drawing source).VerticesSeparated := by
  rw [drawing_eq_normalizedOrthogonalDrawing]
  exact (presentation source).toPlanarPresentation
    |>.normalizedOrthogonalDrawing_verticesSeparated

/-- Exact semantic correctness of the complete source-to-normalized-drawing
pipeline. -/
theorem drawing_correct (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      (drawing source).HasOrientation := by
  rw [drawing_eq_normalizedOrthogonalDrawing]
  exact (problem_correct source).trans
    ((presentation source)
      |>.normalizedOrthogonalDrawing_hasOrientation_iff_satisfiable
        (presentation source).problemWellFormed
        (problem_degreeTwoOrThree source)
        (presentation_separated source)
        (presentation_routesSimple source)).symm

end PeriodicCNFStripReduction
end LeanTrominoes

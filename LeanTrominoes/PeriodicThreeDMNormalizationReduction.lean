import LeanTrominoes.GadgetReductionComputability
import LeanTrominoes.PeriodicThreeDMNormalizationCompileComputability
import LeanTrominoes.PeriodicThreeDMNormalizationOrientationEquivalence
import LeanTrominoes.PeriodicThreeDMNormalizationVertexSeparation
import LeanTrominoes.PeriodicThreeDMNormalizationWellFormed

/-!
# Reduction interface for continuously planar periodic 3DM

This module packages the semantic handoff from a computably generated,
continuously planar periodic 3DM instance to normalized trichromatic
orientation.  The remaining source-specific work only has to generate the
finite problem/drawing data and its geometric certificates.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- A computable many-one source map to continuously planar periodic 3DM,
with exactly the geometric hypotheses consumed by normalization. -/
structure ContinuousPlanarReduction
    {α : Type} [Primcodable α] (source : α → Prop) where
  input : α → Input
  input_computable : Computable input
  presentation :
    ∀ value, (input value).problem.ContinuousPlanarPresentation
  drawing_eq :
    ∀ value, (presentation value).drawing = (input value).drawing
  degree : ∀ value, (input value).problem.DegreeTwoOrThree
  separated : ∀ value,
    (presentation value).drawing.LiftedRoutesAvoidEachOther
  sourceSimple : ∀ value route,
    route ∈ (presentation value).drawing.edgeRoutes →
      LocalIncidenceDrawing.RouteIsSimple route
  correct : ∀ value,
    source value ↔ (input value).problem.Satisfiable

namespace ContinuousPlanarReduction

variable {α : Type} [Primcodable α] {source : α → Prop}
    (reduction : ContinuousPlanarReduction source)

theorem inputOfPresentation_eq (value : α) :
    inputOfPresentation
        (reduction.presentation value).toPlanarPresentation =
      reduction.input value := by
  apply Input.equivData.injective
  apply Prod.ext
  · rfl
  · exact reduction.drawing_eq value

theorem compile_eq (value : α) :
    compile (reduction.input value) =
      (reduction.presentation value).toPlanarPresentation.normalizedOrthogonalDrawing := by
  calc
    compile (reduction.input value) =
        compile (inputOfPresentation
          (reduction.presentation value).toPlanarPresentation) :=
      congrArg compile
        (ContinuousPlanarReduction.inputOfPresentation_eq
          reduction value).symm
    _ = (reduction.presentation value).toPlanarPresentation.normalizedOrthogonalDrawing :=
      compile_inputOfPresentation
        (reduction.presentation value).toPlanarPresentation

/-- The data-only normalization compiler turns any such source map into the
promise-free normalized-orientation reduction consumed by both tromino
gadget libraries. -/
def normalizedOrientationReduction :
    Gadget.NormalizedOrientationReduction source where
  drawing value := compile (reduction.input value)
  drawing_computable :=
    compile_computable.comp reduction.input_computable
  wellFormed value := by
    rw [ContinuousPlanarReduction.compile_eq reduction value]
    exact (reduction.presentation value)
      |>.normalizedOrthogonalDrawing_isWellFormed
        (reduction.presentation value).problemWellFormed
        (reduction.degree value)
        (reduction.separated value)
        (reduction.sourceSimple value)
  verticesSeparated value := by
    rw [ContinuousPlanarReduction.compile_eq reduction value]
    exact (reduction.presentation value).toPlanarPresentation
      |>.normalizedOrthogonalDrawing_verticesSeparated
  correct value := by
    rw [ContinuousPlanarReduction.compile_eq reduction value]
    exact (reduction.correct value).trans
      ((reduction.presentation value)
        |>.normalizedOrthogonalDrawing_hasOrientation_iff_satisfiable
          (reduction.presentation value).problemWellFormed
          (reduction.degree value)
          (reduction.separated value)
          (reduction.sourceSimple value)).symm

end ContinuousPlanarReduction

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes

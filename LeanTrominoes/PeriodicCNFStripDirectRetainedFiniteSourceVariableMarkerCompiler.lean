/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkerCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineFiniteSourceVariableMarkers
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Polynomial-time finite-source variable markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiniteSourceVariableMarkerCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedFiniteSourceVariableMarkerCompilerVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The new fixed-eight input has the same one-per-retained-variable marker
suffix as the existing retained metadata stream. -/
theorem directRetainedFigureNineFiniteSourceVariableMarkers_eq_metadata
    (symbols : List encoding.Γ) :
    directRetainedFigureNineFiniteSourceVariableMarkers decider symbols =
      directRetainedPlanarMetadataVariableMarkers decider symbols := by
  let source :=
    sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols)
  let structural : DecidableEq Variable :=
    fun first second => instDecidableEqProd first second
  calc
    directRetainedFigureNineFiniteSourceVariableMarkers decider symbols =
        @FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
          Variable
          directRetainedFiniteSourceVariableMarkerCompilerVariableDecidableEq
          source := by
      unfold directRetainedFigureNineFiniteSourceVariableMarkers
      exact
        @FormulaShapeRetainedFigureNineDirection.finiteSourceVariableMarkers_eq_retainedMetadata
          Variable
          directRetainedFiniteSourceVariableMarkerCompilerVariableDecidableEq
          (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
            Variable
            directRetainedFiniteSourceVariableMarkerCompilerVariableDecidableEq)
          source
    _ = @FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
          Variable structural source :=
      FormulaShapeRetainedFigureNineDirection.retainedMetadataVariableMarkers_eq_of_decidableEq
        directRetainedFiniteSourceVariableMarkerCompilerVariableDecidableEq
        structural source
    _ = directRetainedPlanarMetadataVariableMarkers decider symbols := by
      rfl

/-- The finite-source marker suffix is polynomial-time computable by
transporting the established retained-metadata compiler. -/
noncomputable def
    directRetainedFigureNineFiniteSourceVariableMarkersComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token id id
      (directRetainedFigureNineFiniteSourceVariableMarkers decider) :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedPlanarMetadataVariableMarkers decider)
    (directRetainedFigureNineFiniteSourceVariableMarkers decider)
    (fun symbols =>
      (directRetainedFigureNineFiniteSourceVariableMarkers_eq_metadata
        decider symbols).symm)
    (directRetainedPlanarMetadataVariableMarkersComputableInPolyTime decider)

/-- Recover the retained source and append the finite-source marker suffix. -/
noncomputable def directRetainedFigureNineFiniteSourceVariableMarkerAppender :
    TM2ComputableInPolyTime id id
      (RetainedInputAppendPipeline.appendFromWorkspace
        (directRetainedFigureNineFiniteSourceVariableMarkers decider)) :=
  RetainedInputAppendPipeline.appendFromWorkspaceComputableInPolyTimeOfCompiler
    (directRetainedFigureNineFiniteSourceVariableMarkers decider)
    (directRetainedFigureNineFiniteSourceVariableMarkersComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end

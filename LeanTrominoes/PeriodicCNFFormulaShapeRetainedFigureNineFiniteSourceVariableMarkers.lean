/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableMarkerCount
import LeanTrominoes.PeriodicEightOccurrenceSplitExactVariableCount

/-! # Retained Figure 9 finite-source variable markers -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit PeriodicOrthocrossing

/-- The retained metadata marker stream is independent of the chosen
decision procedure for source-variable equality. -/
theorem retainedMetadataVariableMarkers_eq_of_decidableEq
    {Variable : Type}
    (first second : DecidableEq Variable)
    (source : PeriodicCNF Variable) :
    @FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
        Variable first source =
      @FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
        Variable second source := by
  have equal : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- The one-per-source-variable input to the fixed-eight expander is exactly
the established retained-planar metadata marker suffix. -/
theorem finiteSourceVariableMarkers_eq_retainedMetadata
    {Variable : Type} [DecidableEq Variable]
    [outputDecidableEq :
      DecidableEq (WrappedPeriodicPlanarSATVariable Variable)]
    (source : PeriodicCNF Variable) :
    List.replicate
        (@PeriodicThreeSATThree.sourceVariables
          (WrappedPeriodicPlanarSATVariable Variable)
          outputDecidableEq
          (sourceScaledForFigureSeven source).erase).length
        FormulaShapeDirectionOrdering.Token.variable =
      FormulaShapeRetainedPlanarMetadataDirection.variableMarkers source := by
  rw [FormulaShapeRetainedPlanarMetadataDirection.variableMarkers_eq_replicate_retainedCount]
  apply congrArg (fun count =>
    List.replicate count FormulaShapeDirectionOrdering.Token.variable)
  let structural :
      DecidableEq (WrappedPeriodicPlanarSATVariable Variable) :=
    @instDecidableEqWrappedPeriodicVariable
      (PeriodicPlanarSATVariable Variable)
      (@instDecidableEqPeriodicPlanarSATVariable Variable _)
  have outputDecidableEqEqual : outputDecidableEq = structural :=
    Subsingleton.elim _ _
  rw [outputDecidableEqEqual]
  rw [@sourceVariables_eq_variableOccurrences_dedup _ structural]
  unfold sourceScaledForFigureSeven
  rw [PositionedPeriodicCNF.erase_scale]
  have sourceEq :
      finalCoordinatedSource source =
        FormulaShapeRetainedPlanarDirection.positionedSource source := by
    rfl
  rw [sourceEq]
  rw [FormulaShapeRetainedPlanarMetadataDirection.finalPositionedSource_variableCount_eq_retainedDrawing]

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes

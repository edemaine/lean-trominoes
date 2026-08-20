/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceData

/-! # Finite shapes of the retained final exact-one formula -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFinalExactOne

/-- Apply the complete finite Figure 9, unit-removal, and polarity profile
transformation to the exact clockwise retained source shape. -/
def shape {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List FormulaShape.Token :=
  FormulaShapeFinalExactOne.shape
    (FormulaShapeRetainedFigureNineSource.shape source)

@[simp] theorem clauseProfiles_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.clauseProfiles (shape source) =
      ClauseProfileFinalExactOne.profiles
        (FormulaShape.clauseProfiles
          (FormulaShapeRetainedFigureNineSource.shape source)) := by
  exact FormulaShapeFinalExactOne.clauseProfiles_shape _

@[simp] theorem variableCount_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.variableCount (shape source) =
      FormulaShape.variableCount
          (FormulaShapeRetainedFigureNineSource.shape source) +
        ((FormulaShape.clauseProfiles
          (FormulaShapeRetainedFigureNineSource.shape source)).map
            FormulaShapeFinalExactOne.clauseFreshVariableCount).sum := by
  exact FormulaShapeFinalExactOne.variableCount_shape _

end FormulaShapeRetainedFinalExactOne
end PeriodicCNF
end LeanTrominoes

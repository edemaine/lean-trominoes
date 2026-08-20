/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarData

/-! # Finite formula shapes after retained fixed-eight splitting -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFixedEight

/-- Apply the finite nine-copy fixed-eight transformation to the canonical
retained-planar shape. -/
def shape {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List FormulaShape.Token :=
  FormulaShapeFixedEight.shape
    (FormulaShapeRetainedPlanar.shape source)

@[simp] theorem clauseProfiles_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.clauseProfiles (shape source) =
      FormulaShape.clauseProfiles
          (FormulaShapeRetainedPlanar.shape source) ++
        FormulaShapeFixedEight.cycleProfiles
          (FormulaShapeRetainedPlanar.shape source) := by
  exact FormulaShapeFixedEight.clauseProfiles_shape _

@[simp] theorem variableCount_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.variableCount (shape source) =
      FormulaShapeFixedEight.copiesPerVariable *
        FormulaShape.variableCount
          (FormulaShapeRetainedPlanar.shape source) := by
  exact FormulaShapeFixedEight.variableCount_shape _

end FormulaShapeRetainedFixedEight
end PeriodicCNF
end LeanTrominoes

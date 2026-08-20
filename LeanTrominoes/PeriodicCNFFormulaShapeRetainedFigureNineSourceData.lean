/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance

/-! # Exact input shapes at the retained Figure 9 boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSource

open PeriodicOrthocrossing

/-- Canonical shape after fixed-eight, clockwise clause ordering, and the
whole-source Figure 9 clearance scale. -/
def shape {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List FormulaShape.Token :=
  FormulaShapeOfFormula.shape
    (retainedFigureNineClearancePositionedFormula source).erase

@[simp] theorem clauseProfiles_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.clauseProfiles (shape source) =
      FormulaShapeOfFormula.profiles
        (retainedFigureNineClearancePositionedFormula source).erase := by
  exact FormulaShapeOfFormula.clauseProfiles_shape _

@[simp] theorem variableCount_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.variableCount (shape source) =
      (retainedFigureNineClearancePositionedFormula
        source).erase.variableOccurrences.dedup.length := by
  exact FormulaShapeOfFormula.variableCount_shape _

end FormulaShapeRetainedFigureNineSource
end PeriodicCNF
end LeanTrominoes

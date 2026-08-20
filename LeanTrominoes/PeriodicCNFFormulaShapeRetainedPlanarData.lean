/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate

/-! # Finite formula shapes of the retained planarization endpoint -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanar

open PeriodicOrthocrossing

/-- Canonical ordered clause-profile and distinct-variable shape of the final
retained, wrapped, gauged, and deduplicated planar-SAT formula. -/
def shape {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List FormulaShape.Token :=
  FormulaShapeOfFormula.shape (retainedPlanarSATFormula source)

@[simp] theorem clauseProfiles_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.clauseProfiles (shape source) =
      FormulaShapeOfFormula.profiles
        (retainedPlanarSATFormula source) := by
  exact FormulaShapeOfFormula.clauseProfiles_shape _

@[simp] theorem variableCount_shape
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    FormulaShape.variableCount (shape source) =
      (retainedPlanarSATFormula source).variableOccurrences.dedup.length := by
  exact FormulaShapeOfFormula.variableCount_shape _

end FormulaShapeRetainedPlanar
end PeriodicCNF
end LeanTrominoes

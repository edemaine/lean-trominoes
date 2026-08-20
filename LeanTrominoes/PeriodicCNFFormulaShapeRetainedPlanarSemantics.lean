/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarData

/-! # Exact semantics of retained planar formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanar

open ClauseProfileOccurrenceSplit
open PeriodicOrthocrossing
open UnaryProgramClauseProfile

/-- The retained planar shape gives the exact clause profiles in presentation
order and the exact number of distinct variables. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (FormulaShape.clauseProfiles (shape source)).map
          ClauseProfile.literals =
        (retainedPlanarSATFormula source).clauses.map literalProfiles ∧
      FormulaShape.variableCount (shape source) =
        (retainedPlanarSATFormula source).variableOccurrences.dedup.length := by
  let certificate := retainedPlanarSATCertificate source sourceLocal
    sourceWidth sourceOccurrences sourceClausesNonempty
  simpa only [shape] using
    FormulaShapeOfFormula.shape_correct
      (retainedPlanarSATFormula source)
      certificate.widthAtMostThree
      certificate.clausesNonempty

end FormulaShapeRetainedPlanar
end PeriodicCNF
end LeanTrominoes

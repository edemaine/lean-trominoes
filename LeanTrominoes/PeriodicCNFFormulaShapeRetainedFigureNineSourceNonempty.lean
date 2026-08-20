/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceData
import LeanTrominoes.PositionedPeriodicCNFEraseNonempty

/-! # Nonempty clauses at the retained Figure 9 source boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSource

open PeriodicOrthocrossing

theorem clausesNonempty
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈
        (retainedFigureNineClearancePositionedFormula source).erase.clauses,
      clause ≠ [] := by
  exact PositionedPeriodicCNF.erase_clausesNonempty_of_clausesNonempty _
    (retainedFigureNineClearancePositionedFormula_clausesNonempty
      source sourceClausesNonempty)

end FormulaShapeRetainedFigureNineSource
end PeriodicCNF
end LeanTrominoes

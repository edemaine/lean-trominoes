/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionFinite
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRoutedDescriptorBlocks

/-! # Finite direction semantics of retained Figure 9 -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

/-- Under the source promises used by the reduction, every copied and cycle
route descriptor in the named phase-major stream is given by its finite
lookup table. -/
theorem routedDescriptors_eq_finiteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    routedDescriptors source = finiteDescriptors source := by
  unfold routedDescriptors finiteDescriptors
  rw [routedCopiedClauseDescriptors_eq_copiedClauseDescriptors
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty,
    routedCycleClauseDescriptors_eq_finiteCycleClauseDescriptors]

/-- The descriptor stream computed from the actual final normalized route
family is exactly the finite copied/cycle lookup stream. -/
theorem descriptors_eq_finiteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    descriptors source = finiteDescriptors source :=
  (descriptors_eq_routedDescriptors source).trans
    (routedDescriptors_eq_finiteDescriptors
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes

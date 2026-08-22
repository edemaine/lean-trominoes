/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalRawClassifier
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData

/-! # Preservation of the internal-atom classifier by normalization -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Periodicization, wrapping, canonical variable gauging, and clause-anchor
normalization preserve whether a metadata clause contains a crossover
internal. -/
theorem normalizedClause_hasCrossoverInternal_eq_embeddedClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    normalizedClauseHasCrossoverInternal
        (normalizedClause source metadata) =
      embeddedClauseHasCrossoverInternal metadata.clause := by
  unfold normalizedClause normalizedClauseHasCrossoverInternal
    embeddedClauseHasCrossoverInternal
    PeriodicClause.anchorNormalize PeriodicClause.variableGauge
    wrapPeriodicPlanarSATClause periodicizePlanarSATClause
  simp only [List.map_map]
  rw [List.any_map]
  change metadata.clause.literals.any (fun literal =>
      wrappedAtomIsCrossoverInternal
        (⟨(normalizePlanarSATVariable source literal.1).1⟩ :
          WrappedPeriodicPlanarSATVariable Variable)) =
    metadata.clause.literals.any fun literal =>
      planarSATAtomIsCrossoverInternal literal.1
  simp only [wrappedAtomIsCrossoverInternal_normalizePlanarSATVariable]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

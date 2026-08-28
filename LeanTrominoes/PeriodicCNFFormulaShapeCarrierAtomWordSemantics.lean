/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizedFamilyNodup
import LeanTrominoes.PeriodicEqualityNormalizedClauseAtomWordSemantics

/-! # Atom-word column of the retained carrier family -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Retained carrier clauses flatten to the repeated endpoint-word block of
each normalized complete-carrier link. -/
theorem carrierMetadataNormalizedClauses_atomWords
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (word : WrappedPeriodicPlanarSATVariable Variable → List Bool) :
    (carrierMetadataNormalizedClauses source).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      ((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source))).flatMap fun link =>
            [word link.first, word link.second,
              word link.first, word link.second] := by
  rw [carrierMetadataNormalizedClauses_eq_normalizedFormulaClauses,
    PeriodicEquality.normalizedFormulaClauses_eq]
  exact PeriodicEquality.normalizedClauses_atomWords _ _

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateData

/-! # Looking up raw representative metadata routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem rawRepresentativeRoute_eq_of_clauseLookup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause : PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? = some clause) :
    rawRepresentativeRoute source clauseIndex literalIndex =
      retainedDrawingPlanarSATLocalIncidenceRoutes source
        ((normalizedClauses source).idxOf clause) literalIndex := by
  unfold rawRepresentativeRoute
  rw [clauseLookup]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

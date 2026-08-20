/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDirectionData
import LeanTrominoes.PeriodicCNFPlanarRetainedGaugedRoutesComputability

/-! # Representative retained routes selected by normalized metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The first normalized source route representing a final deduplicated
clause.  An out-of-range clause index has the same empty-route default as the
canonical final route family. -/
def representativeRoute {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  match (deduplicatedClauses source)[clauseIndex]? with
  | none => []
  | some clause =>
      retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        source ((normalizedClauses source).idxOf clause) literalIndex

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

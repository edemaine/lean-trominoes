/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteData

/-! # Raw retained routes selected by normalized metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The raw finite component route selected by the first metadata record whose
normalized clause represents a final deduplicated clause. -/
def rawRepresentativeRoute {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : List Cell :=
  match (deduplicatedClauses source)[clauseIndex]? with
  | none => []
  | some clause =>
      retainedDrawingPlanarSATLocalIncidenceRoutes source
        ((normalizedClauses source).idxOf clause) literalIndex

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataIncidenceRoutePrefixDirections
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Raw prefix direction words of final coordinated source routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget
open PeriodicCNF

/-- Deleting the old endpoint from a final fallback source route leaves
exactly the raw metadata representative's prefix direction word. -/
theorem finalCoordinatedSourceRoutes_prefixDirections_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (finalCoordinatedSourceRoutes source
          clauseIndex literalIndex).dropLast =
      unitSubdivisionDirections
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.rawRepresentativeRoute
          source clauseIndex literalIndex).dropLast := by
  exact
    PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.incidenceRoutes_prefixDirections_eq_rawRepresentativeRoute
      source clauseIndex literalIndex

end PeriodicOrthocrossing
end LeanTrominoes

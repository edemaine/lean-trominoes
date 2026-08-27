/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteDirections
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Raw direction words of final coordinated source routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget
open PeriodicCNF

/-- The source route inherited by every final fallback has exactly the raw
metadata-route direction word of its stable retained clause representative. -/
theorem finalCoordinatedSourceRoutes_directions_eq_rawRepresentativeRoute
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    unitSubdivisionDirections
        (finalCoordinatedSourceRoutes source clauseIndex literalIndex) =
      unitSubdivisionDirections
        (PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.rawRepresentativeRoute
          source clauseIndex literalIndex) := by
  exact
    PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.incidenceRoutes_directions_eq_rawRepresentativeRoute
      source clauseIndex literalIndex

end PeriodicOrthocrossing
end LeanTrominoes

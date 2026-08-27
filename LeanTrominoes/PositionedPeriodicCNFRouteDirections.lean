/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PositionedPeriodicCNFNormalizedRouteSeparation

/-! # Direction words of canonically translated periodic-CNF routes -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open Gadget
open PeriodicOrthocrossing

/-- Subtracting a clause's common period translation from every route point
leaves its complete segment-major cardinal direction word unchanged. -/
@[simp] theorem unitSubdivisionDirections_normalizeIncidenceRoute
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell) :
    unitSubdivisionDirections
        (normalizeIncidenceRoute placement clause route) =
      unitSubdivisionDirections route := by
  rw [normalizeIncidenceRoute_eq_translate]
  exact unitSubdivisionDirections_translatePolyline _ _

end PositionedPeriodicCNF
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridors

/-! # Proof-free rebasing of occurrence source routes -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PeriodicOrthocrossing

/-- Rebase the stored clause-to-variable route selected by a raw occurrence
slot.  Inactive slots use the empty fallback. -/
def occurrenceSourceRouteFromData
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (entry : Variable × OccurrenceSlot) : List Cell :=
  match occurrenceAt source.erase entry.1 entry.2 with
  | none => []
  | some tagged =>
      let clause :=
        ((source.clauses[tagged.2.1]?).map
          PositionedPeriodicClause.literals).getD []
      translatePolyline
        (placement.translation
          (Cell.sub (PeriodicCNF.clauseAnchor clause) tagged.1.offset))
        (routes tagged.2.1 tagged.2.2).reverse

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

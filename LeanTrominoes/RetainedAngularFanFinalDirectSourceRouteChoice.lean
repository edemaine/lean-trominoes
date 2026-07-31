import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedFinalRouteMacrocellBounds

/-!
# Direct-source route choices in the final retained quotient

The final retained formula anchor-normalizes and deduplicates the finite
planar-SAT clauses.  Its clause indices therefore do not directly index the
raw component metadata used by the coordinated-route atlas.

This file performs the same representative-clause lookup as the final route
construction.  A successful raw direct-source choice is then translated by
the clause's physical anchor-normalization shift.  The result is a total
lookup in the exact coordinates used by the final retained source.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

set_option maxHeartbeats 1200000

/-- Translate only the component origin of a checked route choice. -/
def RetainedDirectSourceRouteChoice.translateOrigin
    (choice : RetainedDirectSourceRouteChoice)
    (offset : Cell) :
    RetainedDirectSourceRouteChoice := {
  origin := Cell.add offset choice.origin
  kind := choice.kind
  index := choice.index
}

/-- Origin translation does not change the local atlas entry or its
direction-matching contract. -/
theorem RetainedDirectSourceRouteChoice.translateOrigin_matches
    {Variable : Type*} [DecidableEq Variable]
    (choice : RetainedDirectSourceRouteChoice)
    (offset : Cell)
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat)
    (directionMatches : choice.Matches formula source literalIndex) :
    (choice.translateOrigin offset).Matches
      formula source literalIndex :=
  directionMatches

/-- Physical anchor-normalization translation attached to one raw retained
metadata entry at final periodic shift zero. -/
def retainedFinalDirectSourceMetadataTranslation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    Cell :=
  (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).translation
    (Cell.sub (0, 0)
      (PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals))

/-- The translated atlas route of a final choice is exactly the displayed
route at the same clause and literal indices of the deduplicated source. -/
def RetainedDirectSourceRouteChoice.RepresentsFinalRoute
    {Variable : Type*} [DecidableEq Variable]
    (choice : RetainedDirectSourceRouteChoice)
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : Prop :=
  translatePolyline choice.origin
      (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula clauseIndex literalIndex

/-- Apply the raw direct selector to an optional metadata representative and
translate a successful choice into the representative's normalized physical
frame. -/
def retainedFinalDirectSourceRouteChoiceFromMetadata?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literalIndex : Nat)
    (metadata? : Option (DrawingPlanarSATClauseMetadata Variable)) :
    Option RetainedDirectSourceRouteChoice :=
  match metadata? with
  | none =>
      none
  | some metadata =>
      match retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex with
      | none =>
          none
      | some choice =>
          some
            (choice.translateOrigin
              (retainedFinalDirectSourceMetadataTranslation
                formula metadata))

/-- Checked direct-source choice for one clause/literal index of the final
retained source.  A candidate is accepted only when its translated atlas
route equals the actual final quotient route.  Missing
final clauses, missing metadata representatives, malformed local indices,
non-direct sources, and failed equality checks all return `none`. -/
def retainedFinalDirectSourceRouteChoice?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    Option RetainedDirectSourceRouteChoice :=
  match
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? with
  | none =>
      none
  | some finalClause =>
      let metadataIndex :=
        (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).representativeClauseIndex finalClause.literals
      match retainedFinalDirectSourceRouteChoiceFromMetadata?
          formula literalIndex
          ((retainedDrawingPlanarSATClauseMetadata
            formula)[metadataIndex]?) with
      | none =>
          none
      | some choice =>
          if
              translatePolyline choice.origin
                  (retainedDirectSourceLocalRouteAt
                    choice.kind choice.index) =
                retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                  formula clauseIndex literalIndex then
            some choice
          else
            none

/-- Explicit final-clause, representative-metadata, and raw-atlas lookups
compose to the corresponding successful final choice. -/
theorem retainedFinalDirectSourceRouteChoice_eq_some_of_lookups
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (finalClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (rawChoice : RetainedDirectSourceRouteChoice)
    (finalClauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? = some finalClause)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata formula)[
          (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).representativeClauseIndex finalClause.literals]? =
        some metadata)
    (rawLookup :
      retainedDirectSourceRouteChoice?
          formula metadata.source literalIndex =
        some rawChoice)
    (represents :
      (rawChoice.translateOrigin
        (retainedFinalDirectSourceMetadataTranslation
          formula metadata)).RepresentsFinalRoute
            formula clauseIndex literalIndex) :
    retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex =
      some
        (rawChoice.translateOrigin
          (retainedFinalDirectSourceMetadataTranslation
            formula metadata)) := by
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
  unfold retainedFinalDirectSourceRouteChoice?
  rw [finalClauseLookup]
  simp only
  rw [metadataLookup]
  simp [retainedFinalDirectSourceRouteChoiceFromMetadata?,
    rawLookup, represents]

/-- Successful final selection carries the checked equality between its
translated atlas route and the actual deduplicated source route. -/
theorem retainedFinalDirectSourceRouteChoice_representsFinalRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    choice.RepresentsFinalRoute
      formula clauseIndex literalIndex := by
  unfold retainedFinalDirectSourceRouteChoice? at choiceLookup
  split at choiceLookup
  next => cases choiceLookup
  next =>
    simp only at choiceLookup
    split at choiceLookup
    next => cases choiceLookup
    next selected =>
      split at choiceLookup
      next represented =>
        simp only [Option.some.injEq] at choiceLookup
        subst choice
        exact represented
      next => cases choiceLookup

/-- Translation commutes with the defaulted head of a nonempty polyline. -/
private theorem translatePolyline_headD
    (offset : Cell) (route : List Cell)
    (nonempty : 0 < route.length) :
    (translatePolyline offset route).headD (0, 0) =
      Cell.add offset (route.headD (0, 0)) := by
  cases route with
  | nil => simp at nonempty
  | cons head tail =>
      simp [translatePolyline]

/-- Translation commutes with the defaulted last point of a nonempty
polyline. -/
private theorem translatePolyline_getLastD
    (offset : Cell) (route : List Cell)
    (nonempty : 0 < route.length) :
    (translatePolyline offset route).getLastD (0, 0) =
      Cell.add offset (route.getLastD (0, 0)) := by
  have routeNe : route ≠ [] := List.ne_nil_of_length_pos nonempty
  simp [translatePolyline, List.getLast?_map,
    List.getLast?_eq_getLast_of_ne_nil routeNe]

/-- The actual final quotient route selected by a successful choice begins
at the translated local-atlas head. -/
theorem retainedFinalDirectSourceRouteChoice_route_headD
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula clauseIndex literalIndex).headD (0, 0) =
      Cell.add choice.origin
        ((retainedDirectSourceLocalRouteAt
          choice.kind choice.index).headD (0, 0)) := by
  have represents :=
    retainedFinalDirectSourceRouteChoice_representsFinalRoute
      formula clauseIndex literalIndex choice choiceLookup
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
  rw [← represents]
  exact translatePolyline_headD choice.origin
    (retainedDirectSourceLocalRouteAt choice.kind choice.index)
    (by rw [retainedDirectSourceLocalRouteAt_length]; omega)

/-- The actual final quotient route selected by a successful choice ends at
the translated local-atlas last point. -/
theorem retainedFinalDirectSourceRouteChoice_route_getLastD
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula clauseIndex literalIndex).getLastD (0, 0) =
      Cell.add choice.origin
        ((retainedDirectSourceLocalRouteAt
          choice.kind choice.index).getLastD (0, 0)) := by
  have represents :=
    retainedFinalDirectSourceRouteChoice_representsFinalRoute
      formula clauseIndex literalIndex choice choiceLookup
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
  rw [← represents]
  exact translatePolyline_getLastD choice.origin
    (retainedDirectSourceLocalRouteAt choice.kind choice.index)
    (by rw [retainedDirectSourceLocalRouteAt_length]; omega)

/-- Every successful final choice provides an orthogonal complete coordinated
route in the final retained source coordinates. -/
theorem retainedFinalDirectSourceRouteChoice_completeRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (_choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (slot : RetainedTerminalSlot) :
    OrthogonalPolyline (choice.completeRoute slot) := by
  exact choice.completeRoute_orthogonal slot

end PeriodicEightOccurrenceSplit
end LeanTrominoes

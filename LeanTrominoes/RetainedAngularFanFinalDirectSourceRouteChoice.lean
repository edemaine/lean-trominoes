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
retained source.  Missing final clauses, missing metadata representatives,
malformed local indices, and non-direct sources all return `none`. -/
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
      retainedFinalDirectSourceRouteChoiceFromMetadata?
        formula literalIndex
        ((retainedDrawingPlanarSATClauseMetadata
          formula)[metadataIndex]?)

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
        some rawChoice) :
    retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex =
      some
        (rawChoice.translateOrigin
          (retainedFinalDirectSourceMetadataTranslation
            formula metadata)) := by
  unfold retainedFinalDirectSourceRouteChoice?
  rw [finalClauseLookup]
  simp only
  rw [metadataLookup]
  simp [retainedFinalDirectSourceRouteChoiceFromMetadata?,
    rawLookup]

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

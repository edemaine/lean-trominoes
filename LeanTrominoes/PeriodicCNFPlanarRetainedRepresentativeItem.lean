import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteOccurrences

/-!
# Retained representative-indexed data

Auxiliary data attached to the finite retained clauses is transported to the
final deduplicated quotient through the first source representative of each
final clause.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Look up auxiliary finite-clause data for one clause of the final retained
quotient. -/
def retainedRepresentativeItem?
    {Variable Item : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (items : List Item) (finalClauseIndex : Nat) : Option Item :=
  PositionedPeriodicCNF.representativeItem?
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    items finalClauseIndex

/-- Raw final-clause and source-representative lookups compose to the
retained representative-item lookup. -/
theorem retainedRepresentativeItem?_eq_some_of_lookups
    {Variable Item : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (items : List Item) (finalClauseIndex : Nat)
    (finalClause :
      PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (item : Item)
    (finalClauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[finalClauseIndex]? = some finalClause)
    (itemLookup :
      items[
        (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).representativeClauseIndex finalClause.literals]? =
        some item) :
    retainedRepresentativeItem? formula items finalClauseIndex =
      some item := by
  unfold retainedRepresentativeItem?
  exact PositionedPeriodicCNF.representativeItem?_eq_some_of_lookups
    _ _ _ _ finalClause item finalClauseLookup itemLookup

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.PeriodicCNFPlanarRetainedGaugedRoutesComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedRepresentativeItem

/-!
# Computability of retained representative-indexed data

The final retained quotient selects auxiliary data through the first source
clause representing each deduplicated final clause.  This module specializes
the generic representative-item lookup once to the large wrapped planar-SAT
source, keeping that type-level specialization out of downstream proofs.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 3000000

/-- Looking up any primitive-recursive auxiliary list through the retained
final clause representative is primitive recursive. -/
theorem retainedRepresentativeItem?_primrec
    {Variable Item : Type*}
    [Primcodable Variable] [Primcodable Item] [DecidableEq Variable]
    (items : PeriodicCNF Variable → List Item)
    (itemsPrimrec : Primrec items) :
    Primrec fun input : PeriodicCNF Variable × Nat =>
      retainedRepresentativeItem? input.1 (items input.1) input.2 := by
  exact (PositionedPeriodicCNF.representativeItem?_primrec
    (Input := PeriodicCNF Variable)
    (Variable := WrappedPeriodicPlanarSATVariable Variable)
    (Item := Item)
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    items
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    itemsPrimrec).of_eq fun input => by
      unfold retainedRepresentativeItem?
      rfl

end PeriodicOrthocrossing
end LeanTrominoes

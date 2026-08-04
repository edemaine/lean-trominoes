import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements
import LeanTrominoes.PeriodicMacrocellGeometry

/-!
# Local vertex codes for the final two-stage Figure 9 macrocell

The Figure 9 replacement refines by `12`, and unit elimination refines once
more by `6`.  Thus every final variable or clause vertex is a base vertex
refined by a `72 × 72` local code.  This file enumerates a harmless superset
of the possible codes and verifies their two key finite properties:
distinct addresses have distinct coordinates, and every coordinate lies in
the half-open macrocell.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Total refinement factor of Figure 9 followed by unit elimination. -/
def finalFigureNineMacrocellScale : Nat := 72

/-- The six possible local clause offsets used by unit elimination.  Some
cases cannot occur after Figure 9, but retaining all of them makes the local
code interface independent of arity provenance. -/
inductive FinalUnitClauseLocal
  | emptyFirst
  | emptySecond
  | emptyThird
  | unitFirst
  | unitSecond
  | ordinary
  deriving DecidableEq, Repr, Fintype

/-- Local unit-elimination clause position selected by its arity case. -/
def FinalUnitClauseLocal.position : FinalUnitClauseLocal → Cell
  | .emptyFirst => (3, 1)
  | .emptySecond => (5, 4)
  | .emptyThird => (1, 4)
  | .unitFirst => (3, 2)
  | .unitSecond => (3, 4)
  | .ordinary => (3, 3)

/-- A finite address for every kind of vertex that can occur after both
clause-replacement layers. -/
inductive FinalFigureNineLocalAddress
  | inheritedVariable
  | figureNineAuxiliary (kind : OneInThreeAux)
  | unitEliminationAuxiliary
      (figureNineClauseIndex : Fin 6)
      (kind : OneInThreeNoUnitAux)
  | finalClause
      (figureNineClauseIndex : Fin 6)
      (kind : FinalUnitClauseLocal)
  deriving DecidableEq, Repr, Fintype

/-- The Figure 9 generated-clause offset at a valid local clause index. -/
def finalFigureNineClauseLocalPosition
    (figureNineClauseIndex : Fin 6) : Cell :=
  PlanarOneInThree.generatedClausePosition
    (0, 0) figureNineClauseIndex

/-- Exact local coordinate represented by a final vertex address. -/
def FinalFigureNineLocalAddress.position :
    FinalFigureNineLocalAddress → Cell
  | .inheritedVariable => (0, 0)
  | .figureNineAuxiliary kind =>
      Cell.scale
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale
        (PeriodicOneInThreePositioned.auxiliaryLocalPosition kind)
  | .unitEliminationAuxiliary figureNineClauseIndex kind =>
      Cell.add
        (Cell.scale
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale
          (finalFigureNineClauseLocalPosition figureNineClauseIndex))
        (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind)
  | .finalClause figureNineClauseIndex kind =>
      Cell.add
        (Cell.scale
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale
          (finalFigureNineClauseLocalPosition figureNineClauseIndex))
        kind.position

/-- The finite local code table has no collisions. -/
theorem finalFigureNineLocalAddress_position_injective :
    Function.Injective FinalFigureNineLocalAddress.position := by
  native_decide +revert

/-- Every final local code lies in the half-open `72 × 72` macrocell. -/
theorem finalFigureNineLocalAddress_position_halfOpen
    (address : FinalFigureNineLocalAddress) :
    Cell.PositionInHalfOpenMacrocell
      finalFigureNineMacrocellScale address.position := by
  native_decide +revert

end PeriodicOrthocrossing
end LeanTrominoes

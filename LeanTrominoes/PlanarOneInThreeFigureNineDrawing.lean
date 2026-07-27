import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements

/-!
# Certified local drawing of the full Figure 9 exact-one gadget

The semantic Figure 9 replacement turns a three-literal disjunction into
three exact-one clauses.  This file supplies the missing local geometric
certificate for that full-width case.  Its three source variables are
boundary ports; the four fresh choice/slack variables and all generated
clauses use the coordinates already chosen by `PlanarOneInThree` and
`PeriodicOneInThreePositioned`.

Short source clauses and the subsequent unit-elimination gadgets are handled
in later modules.  Keeping the full-width core separate makes the reusable
planar part of the replacement explicit.
-/

namespace LeanTrominoes
namespace PlanarOneInThree

open PlanarThreeSAT

/-- Variables visible in one full-width Figure 9 neighborhood. -/
inductive FigureNineVariable
  | sourceFirst
  | sourceSecond
  | sourceThird
  | firstChoice
  | secondChoice
  | firstSlack
  | secondSlack
  deriving DecidableEq, Repr, Fintype

/-- The three source incidences enter through the top, left, and right
boundary ports; auxiliary variables occupy their established local
coordinates. -/
def figureNineVariablePosition : FigureNineVariable → Cell
  | .sourceFirst => (6, 0)
  | .sourceSecond => (0, 5)
  | .sourceThird => (12, 5)
  | .firstChoice =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .firstChoice
  | .secondChoice =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .secondChoice
  | .firstSlack =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .firstSlack
  | .secondSlack =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .secondSlack

/-- One embedded exact-one clause at the named Figure 9 position. -/
def figureNineClause
    (index : Nat)
    (literals : List (FigureNineVariable × Bool)) :
    EmbeddedClause FigureNineVariable where
  position := generatedClausePosition (0, 0) index
  literals := literals

/-- The three exact-one clauses in the full-width Figure 9 core.

The Boolean labels reproduce `PeriodicOneInThree.disjunctionGadget`;
geometry depends only on the variable endpoints. -/
def figureNineFormula : List (EmbeddedClause FigureNineVariable) :=
  [figureNineClause 0
      [(.sourceFirst, true), (.firstChoice, true),
        (.secondChoice, true)],
    figureNineClause 1
      [(.sourceSecond, false), (.firstChoice, true),
        (.firstSlack, true)],
    figureNineClause 2
      [(.sourceThird, false), (.secondChoice, true),
        (.secondSlack, true)]]

/-- Explicit rectilinear route for each of the nine Figure 9 incidences. -/
def figureNineRoute
    (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(6, 2), (6, 0)]
  | 0, 1 => [(6, 2), (5, 2), (5, 3), (4, 3)]
  | 0, 2 => [(6, 2), (7, 2), (7, 3), (8, 3)]
  | 1, 0 => [(3, 5), (0, 5)]
  | 1, 1 => [(3, 5), (3, 3), (4, 3)]
  | 1, 2 => [(3, 5), (3, 7), (2, 7)]
  | 2, 0 => [(9, 5), (12, 5)]
  | 2, 1 => [(9, 5), (9, 3), (8, 3)]
  | 2, 2 => [(9, 5), (9, 7), (10, 7)]
  | _, _ => []

/-- Complete finite incidence drawing of the three-clause Figure 9 core. -/
def figureNineDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineVariable where
  formula := figureNineFormula
  variablePosition := figureNineVariablePosition
  routes := figureNineRoute

/-- The full-width Figure 9 core has exact endpoints, orthogonal routes, and
exact continuous planarity. -/
theorem figureNineDrawing_isValid :
    figureNineDrawing.IsValid := by
  native_decide

/-- Endpoint compatibility of the certified local Figure 9 replacement. -/
theorem figureNineDrawing_routesMatch :
    figureNineDrawing.RoutesMatch :=
  figureNineDrawing_isValid.1

/-- Every local Figure 9 incidence is rectilinear. -/
theorem figureNineDrawing_isOrthogonal :
    figureNineDrawing.IsOrthogonal :=
  figureNineDrawing_isValid.2.1

/-- The nine local incidences and all local vertices are continuously
planar. -/
theorem figureNineDrawing_isPlanar :
    figureNineDrawing.IsPlanar :=
  figureNineDrawing_isValid.2.2

end PlanarOneInThree
end LeanTrominoes

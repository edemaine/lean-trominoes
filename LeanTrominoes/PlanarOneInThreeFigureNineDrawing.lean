import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements

/-!
# Certified local drawings of the Figure 9 exact-one gadget

The semantic Figure 9 replacement turns a three-literal disjunction into
three exact-one clauses.  This file supplies the missing local geometric
certificate for source clauses of every arity from zero through three.
Present source variables are boundary ports; the four fresh choice/slack
variables, padding variables, and all generated clauses use the coordinates
already chosen by `PlanarOneInThree` and
`PeriodicOneInThreePositioned`.  For short source clauses, the drawing also
includes the unit exact-one clauses that force missing literals false.

The subsequent elimination of those unit clauses is handled separately.
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
  | firstPadding
  | secondPadding
  | thirdPadding
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
  | .firstPadding =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .firstPadding
  | .secondPadding =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .secondPadding
  | .thirdPadding =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition .thirdPadding

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

/-! ## Short source clauses -/

/-- The Figure 9 replacement of a two-literal source clause: the missing
third literal is represented by a fresh padding variable, followed by a unit
clause forcing that variable false. -/
def figureNineTwoFormula : List (EmbeddedClause FigureNineVariable) :=
  [figureNineClause 0
      [(.sourceFirst, true), (.firstChoice, true),
        (.secondChoice, true)],
    figureNineClause 1
      [(.sourceSecond, false), (.firstChoice, true),
        (.firstSlack, true)],
    figureNineClause 2
      [(.thirdPadding, false), (.secondChoice, true),
        (.secondSlack, true)],
    figureNineClause 3 [(.thirdPadding, false)]]

/-- Explicit routes for the padded two-literal Figure 9 neighborhood. -/
def figureNineTwoRoute
    (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(6, 2), (6, 0)]
  | 0, 1 => [(6, 2), (5, 2), (5, 3), (4, 3)]
  | 0, 2 => [(6, 2), (7, 2), (7, 3), (8, 3)]
  | 1, 0 => [(3, 5), (0, 5)]
  | 1, 1 => [(3, 5), (3, 3), (4, 3)]
  | 1, 2 => [(3, 5), (3, 7), (2, 7)]
  | 2, 0 => [(9, 5), (8, 5), (8, 8), (9, 8)]
  | 2, 1 => [(9, 5), (9, 3), (8, 3)]
  | 2, 2 => [(9, 5), (10, 5), (10, 7)]
  | 3, 0 => [(3, 10), (3, 9), (9, 9), (9, 8)]
  | _, _ => []

/-- Complete drawing of the padded two-literal Figure 9 neighborhood. -/
def figureNineTwoDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineVariable where
  formula := figureNineTwoFormula
  variablePosition := figureNineVariablePosition
  routes := figureNineTwoRoute

/-- The padded two-literal Figure 9 neighborhood is a valid continuous
orthogonal drawing. -/
theorem figureNineTwoDrawing_isValid :
    figureNineTwoDrawing.IsValid := by
  native_decide

/-- The Figure 9 replacement of a one-literal source clause, including the
two padding variables and their forced-false unit clauses. -/
def figureNineOneFormula : List (EmbeddedClause FigureNineVariable) :=
  [figureNineClause 0
      [(.sourceFirst, true), (.firstChoice, true),
        (.secondChoice, true)],
    figureNineClause 1
      [(.secondPadding, false), (.firstChoice, true),
        (.firstSlack, true)],
    figureNineClause 2
      [(.thirdPadding, false), (.secondChoice, true),
        (.secondSlack, true)],
    figureNineClause 3 [(.secondPadding, false)],
    figureNineClause 4 [(.thirdPadding, false)]]

/-- Explicit routes for the padded one-literal Figure 9 neighborhood. -/
def figureNineOneRoute
    (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(6, 2), (6, 0)]
  | 0, 1 => [(6, 2), (5, 2), (5, 3), (4, 3)]
  | 0, 2 => [(6, 2), (7, 2), (7, 3), (8, 3)]
  | 1, 0 => [(3, 5), (4, 5), (4, 8), (6, 8)]
  | 1, 1 => [(3, 5), (3, 3), (4, 3)]
  | 1, 2 => [(3, 5), (3, 7), (2, 7)]
  | 2, 0 => [(9, 5), (8, 5), (8, 8), (9, 8)]
  | 2, 1 => [(9, 5), (9, 3), (8, 3)]
  | 2, 2 => [(9, 5), (10, 5), (10, 7)]
  | 3, 0 => [(3, 10), (3, 9), (6, 9), (6, 8)]
  | 4, 0 => [(6, 10), (7, 10), (7, 9), (9, 9), (9, 8)]
  | _, _ => []

/-- Complete drawing of the padded one-literal Figure 9 neighborhood. -/
def figureNineOneDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineVariable where
  formula := figureNineOneFormula
  variablePosition := figureNineVariablePosition
  routes := figureNineOneRoute

/-- The padded one-literal Figure 9 neighborhood is a valid continuous
orthogonal drawing. -/
theorem figureNineOneDrawing_isValid :
    figureNineOneDrawing.IsValid := by
  native_decide

/-- The Figure 9 replacement of an empty source clause, including all three
padding variables and their forced-false unit clauses. -/
def figureNineZeroFormula : List (EmbeddedClause FigureNineVariable) :=
  [figureNineClause 0
      [(.firstPadding, true), (.firstChoice, true),
        (.secondChoice, true)],
    figureNineClause 1
      [(.secondPadding, false), (.firstChoice, true),
        (.firstSlack, true)],
    figureNineClause 2
      [(.thirdPadding, false), (.secondChoice, true),
        (.secondSlack, true)],
    figureNineClause 3 [(.firstPadding, false)],
    figureNineClause 4 [(.secondPadding, false)],
    figureNineClause 5 [(.thirdPadding, false)]]

/-- Explicit routes for the padded empty-clause Figure 9 neighborhood. -/
def figureNineZeroRoute
    (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(6, 2), (6, 1), (1, 1), (1, 8), (3, 8)]
  | 0, 1 => [(6, 2), (5, 2), (5, 3), (4, 3)]
  | 0, 2 => [(6, 2), (7, 2), (7, 3), (8, 3)]
  | 1, 0 => [(3, 5), (4, 5), (4, 8), (6, 8)]
  | 1, 1 => [(3, 5), (3, 3), (4, 3)]
  | 1, 2 => [(3, 5), (3, 7), (2, 7)]
  | 2, 0 => [(9, 5), (8, 5), (8, 8), (9, 8)]
  | 2, 1 => [(9, 5), (9, 3), (8, 3)]
  | 2, 2 => [(9, 5), (10, 5), (10, 7)]
  | 3, 0 => [(3, 10), (3, 8)]
  | 4, 0 => [(6, 10), (6, 8)]
  | 5, 0 => [(9, 10), (9, 8)]
  | _, _ => []

/-- Complete drawing of the padded empty-clause Figure 9 neighborhood. -/
def figureNineZeroDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineVariable where
  formula := figureNineZeroFormula
  variablePosition := figureNineVariablePosition
  routes := figureNineZeroRoute

/-- The padded empty-clause Figure 9 neighborhood is a valid continuous
orthogonal drawing. -/
theorem figureNineZeroDrawing_isValid :
    figureNineZeroDrawing.IsValid := by
  native_decide

/-! ## Correspondence with the semantic Figure 9 transformation -/

/-- Canonical source-variable roles used to compare the finite templates
with `PlanarOneInThree.clauseGadget`. -/
inductive FigureNineSourceVariable
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- Rename the actual scoped output variables of a canonical Figure 9
replacement to their finite drawing roles. -/
def figureNineOutputRole :
    OneInThreeVariable FigureNineSourceVariable →
      FigureNineVariable
  | .inl .first => .sourceFirst
  | .inl .second => .sourceSecond
  | .inl .third => .sourceThird
  | .inr (_, .firstChoice) => .firstChoice
  | .inr (_, .secondChoice) => .secondChoice
  | .inr (_, .firstSlack) => .firstSlack
  | .inr (_, .secondSlack) => .secondSlack
  | .inr (_, .firstPadding) => .firstPadding
  | .inr (_, .secondPadding) => .secondPadding
  | .inr (_, .thirdPadding) => .thirdPadding

/-- A canonical source clause at the origin with positive literals in the
given role order. -/
def canonicalFigureNineSource
    (roles : List FigureNineSourceVariable) :
    EmbeddedClause FigureNineSourceVariable where
  position := (0, 0)
  literals := roles.map fun role => (role, true)

/-- Run the actual semantic/positioned Figure 9 replacement and rename its
scoped output variables to the finite local roles. -/
def generatedFigureNineTemplate
    (roles : List FigureNineSourceVariable) :
    List (EmbeddedClause FigureNineVariable) :=
  (clauseGadget 0
    (canonicalFigureNineSource roles)).map fun generated =>
      generated.rename figureNineOutputRole

/-- The full finite drawing formula is exactly the positioned semantic
replacement of a canonical ternary source clause. -/
theorem generatedFigureNineTemplate_three :
    generatedFigureNineTemplate [.first, .second, .third] =
      figureNineFormula := by
  native_decide

/-- The padded binary drawing formula is exactly the corresponding
positioned semantic replacement. -/
theorem generatedFigureNineTemplate_two :
    generatedFigureNineTemplate [.first, .second] =
      figureNineTwoFormula := by
  native_decide

/-- The padded unit drawing formula is exactly the corresponding positioned
semantic replacement. -/
theorem generatedFigureNineTemplate_one :
    generatedFigureNineTemplate [.first] =
      figureNineOneFormula := by
  native_decide

/-- The padded empty drawing formula is exactly the corresponding positioned
semantic replacement. -/
theorem generatedFigureNineTemplate_zero :
    generatedFigureNineTemplate [] =
      figureNineZeroFormula := by
  native_decide

end PlanarOneInThree
end LeanTrominoes

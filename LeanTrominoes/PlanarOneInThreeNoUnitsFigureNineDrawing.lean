import LeanTrominoes.PlanarOneInThreeFigureNineDrawing
import LeanTrominoes.PlanarOneInThreeNoUnitsDrawing

/-!
# Certified Figure 9 followed by unit elimination

The separate Figure 9 and unit-elimination drawings are each planar inside
their own refinement cells.  Composing them requires more care: an inherited
Figure 9 route can remain inside the refined `6 × 6` unit-elimination cell
after its first listed point, so merely replacing its first segment can
introduce a crossing.

This file starts the composed geometric certificate with a full-width source
clause.  Every Figure 9 clause is ternary, hence retained by unit elimination.
The displayed routes consist of:

* the retained-clause route to its unit-elimination boundary port;
* a coordinated connector to the first inherited route point outside that
  closed `6 × 6` cell; and
* the remaining scaled Figure 9 route.

The resulting finite checker certificate proves continuous planarity of the
whole two-stage neighborhood, not just of its individual gadgets.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Variables that can occur after applying unit elimination to a Figure 9
neighborhood.  The full-width case below uses only inherited variables;
shorter source clauses also use auxiliaries scoped to a Figure 9 clause. -/
inductive FigureNineNoUnitsVariable
  | inherited (source : PlanarOneInThree.FigureNineVariable)
  | unitAux (sourceClauseIndex : Nat) (kind : OneInThreeNoUnitAux)
  deriving DecidableEq, Repr

/-- Physical positions after the sixfold unit-elimination refinement. -/
def variablePosition : FigureNineNoUnitsVariable → Cell
  | .inherited source =>
      Cell.scale 6
        (PlanarOneInThree.figureNineVariablePosition source)
  | .unitAux sourceClauseIndex kind =>
      Cell.add
        (Cell.scale 6
          (PlanarOneInThree.generatedClausePosition
            (0, 0) sourceClauseIndex))
        (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind)

/-- One clause in the composed finite neighborhood. -/
def clause
    (position : Cell)
    (literals : List (FigureNineNoUnitsVariable × Bool)) :
    EmbeddedClause FigureNineNoUnitsVariable where
  position := position
  literals := literals

/-- The full-width Figure 9 formula after the three ternary clauses have
passed unchanged through unit elimination. -/
def fullFormula : List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .sourceFirst, true),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .sourceSecond, false),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .sourceThird, false),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]]

/-- Coordinated routes for the full-width composed neighborhood.

Each route begins with the appropriate retained-clause port route, then
reaches the first point of the scaled Figure 9 route outside the surrounding
closed `6 × 6` macrocell. -/
def fullRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(39, 15), (39, 12), (36, 12), (36, 0)]
  | 0, 1 =>
      [(39, 15), (36, 15), (31, 15), (31, 12), (30, 12),
        (30, 18), (24, 18)]
  | 0, 2 => [(39, 15), (42, 15), (48, 15), (48, 18)]
  | 1, 0 =>
      [(21, 33), (21, 30), (25, 30), (25, 35), (19, 35),
        (19, 43), (0, 43), (0, 30)]
  | 1, 1 => [(21, 33), (18, 33), (18, 18), (24, 18)]
  | 1, 2 =>
      [(21, 33), (24, 33), (24, 34), (18, 34), (18, 42),
        (12, 42)]
  | 2, 0 => [(57, 33), (57, 30), (72, 30)]
  | 2, 1 => [(57, 33), (54, 33), (54, 18), (48, 18)]
  | 2, 2 =>
      [(57, 33), (60, 33), (60, 34), (54, 34), (54, 42),
        (60, 42)]
  | _, _ => []

/-- Complete two-stage drawing for a full-width Figure 9 neighborhood. -/
def fullDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := fullFormula
  variablePosition := variablePosition
  routes := fullRoute

/-- The whole full-width two-stage neighborhood has exact endpoints,
orthogonal simple routes, vertex avoidance, and continuous pairwise
planarity. -/
theorem fullDrawing_isValid : fullDrawing.IsValid := by
  native_decide

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

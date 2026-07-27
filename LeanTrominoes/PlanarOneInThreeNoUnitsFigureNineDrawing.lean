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

/-! ## Short source clauses -/

/-- The two clauses replacing one forced-false padding unit. -/
def forcedFalseUnitReplacement
    (sourceClauseIndex : Nat)
    (source : PlanarOneInThree.FigureNineVariable) :
    List (EmbeddedClause FigureNineNoUnitsVariable) :=
  let origin :=
    Cell.scale 6
      (PlanarOneInThree.generatedClausePosition
        (0, 0) sourceClauseIndex)
  [clause (Cell.add origin (3, 2))
      [(.inherited source, true),
        (.unitAux sourceClauseIndex .first, true),
        (.unitAux sourceClauseIndex .second, true)],
    clause (Cell.add origin (3, 4))
      [(.unitAux sourceClauseIndex .first, true),
        (.unitAux sourceClauseIndex .second, true)]]

/-- Figure 9 for a binary source clause after eliminating its one padding
unit clause. -/
def twoFormula : List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .sourceFirst, true),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .sourceSecond, false),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .thirdPadding, false),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]] ++
    forcedFalseUnitReplacement 3 .thirdPadding

/-- Coordinated routes for the binary-source composed neighborhood. -/
def twoRoute (clauseIndex literalIndex : Nat) : List Cell :=
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
  | 2, 0 =>
      [(57, 33), (57, 30), (48, 30), (48, 48), (54, 48)]
  | 2, 1 =>
      [(57, 33), (54, 33), (54, 34), (59, 34), (59, 43),
        (61, 43), (61, 32), (58, 32), (58, 29), (54, 29),
        (54, 18), (48, 18)]
  | 2, 2 => [(57, 33), (60, 33), (60, 42)]
  | 3, 0 =>
      [(21, 62), (21, 60), (18, 60), (18, 54), (54, 54),
        (54, 48)]
  | 3, 1 => [(21, 62), (20, 62), (20, 63)]
  | 3, 2 => [(21, 62), (22, 62), (22, 63)]
  | 4, 0 => [(21, 64), (20, 64), (20, 63)]
  | 4, 1 => [(21, 64), (22, 64), (22, 63)]
  | _, _ => []

/-- Complete two-stage drawing for a binary source clause. -/
def twoDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := twoFormula
  variablePosition := variablePosition
  routes := twoRoute

/-- The complete binary-source two-stage neighborhood is continuously
planar. -/
theorem twoDrawing_isValid : twoDrawing.IsValid := by
  native_decide

/-- Figure 9 for a unit source clause after eliminating its two padding unit
clauses. -/
def oneFormula : List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .sourceFirst, true),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .secondPadding, false),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .thirdPadding, false),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]] ++
    forcedFalseUnitReplacement 3 .secondPadding ++
    forcedFalseUnitReplacement 4 .thirdPadding

/-- Coordinated routes for the unit-source composed neighborhood. -/
def oneRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(39, 15), (39, 12), (36, 12), (36, 0)]
  | 0, 1 =>
      [(39, 15), (36, 15), (31, 15), (31, 12), (30, 12),
        (30, 18), (24, 18)]
  | 0, 2 => [(39, 15), (42, 15), (48, 15), (48, 18)]
  | 1, 0 =>
      [(21, 33), (21, 30), (25, 30), (25, 35), (24, 35),
        (24, 48), (36, 48)]
  | 1, 1 => [(21, 33), (18, 33), (18, 18), (24, 18)]
  | 1, 2 =>
      [(21, 33), (24, 33), (24, 34), (18, 34), (18, 42),
        (12, 42)]
  | 2, 0 =>
      [(57, 33), (57, 30), (48, 30), (48, 48), (54, 48)]
  | 2, 1 =>
      [(57, 33), (54, 33), (54, 34), (59, 34), (59, 43),
        (61, 43), (61, 32), (58, 32), (58, 29), (54, 29),
        (54, 18), (48, 18)]
  | 2, 2 => [(57, 33), (60, 33), (60, 42)]
  | 3, 0 =>
      [(21, 62), (21, 60), (18, 60), (18, 54), (36, 54),
        (36, 48)]
  | 3, 1 => [(21, 62), (20, 62), (20, 63)]
  | 3, 2 => [(21, 62), (22, 62), (22, 63)]
  | 4, 0 => [(21, 64), (20, 64), (20, 63)]
  | 4, 1 => [(21, 64), (22, 64), (22, 63)]
  | 5, 0 =>
      [(39, 62), (39, 60), (42, 60), (42, 54), (54, 54),
        (54, 48)]
  | 5, 1 => [(39, 62), (38, 62), (38, 63)]
  | 5, 2 => [(39, 62), (40, 62), (40, 63)]
  | 6, 0 => [(39, 64), (38, 64), (38, 63)]
  | 6, 1 => [(39, 64), (40, 64), (40, 63)]
  | _, _ => []

/-- Complete two-stage drawing for a unit source clause. -/
def oneDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := oneFormula
  variablePosition := variablePosition
  routes := oneRoute

/-- The complete unit-source two-stage neighborhood is continuously planar. -/
theorem oneDrawing_isValid : oneDrawing.IsValid := by
  native_decide

/-- Figure 9 for an empty source clause after eliminating all three padding
unit clauses. -/
def zeroFormula : List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .firstPadding, true),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .secondPadding, false),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .thirdPadding, false),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]] ++
    forcedFalseUnitReplacement 3 .firstPadding ++
    forcedFalseUnitReplacement 4 .secondPadding ++
    forcedFalseUnitReplacement 5 .thirdPadding

/-- Coordinated routes for the empty-source composed neighborhood. -/
def zeroRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 =>
      [(39, 15), (39, 12), (36, 12), (36, 6), (6, 6),
        (6, 48), (18, 48)]
  | 0, 1 =>
      [(39, 15), (36, 15), (31, 15), (31, 12), (30, 12),
        (30, 18), (24, 18)]
  | 0, 2 => [(39, 15), (42, 15), (48, 15), (48, 18)]
  | 1, 0 =>
      [(21, 33), (21, 30), (25, 30), (25, 35), (24, 35),
        (24, 48), (36, 48)]
  | 1, 1 => [(21, 33), (18, 33), (18, 18), (24, 18)]
  | 1, 2 =>
      [(21, 33), (24, 33), (24, 34), (18, 34), (18, 42),
        (12, 42)]
  | 2, 0 =>
      [(57, 33), (57, 30), (48, 30), (48, 48), (54, 48)]
  | 2, 1 =>
      [(57, 33), (54, 33), (54, 34), (59, 34), (59, 43),
        (61, 43), (61, 32), (58, 32), (58, 29), (54, 29),
        (54, 18), (48, 18)]
  | 2, 2 => [(57, 33), (60, 33), (60, 42)]
  | 3, 0 => [(21, 62), (21, 60), (18, 60), (18, 48)]
  | 3, 1 => [(21, 62), (20, 62), (20, 63)]
  | 3, 2 => [(21, 62), (22, 62), (22, 63)]
  | 4, 0 => [(21, 64), (20, 64), (20, 63)]
  | 4, 1 => [(21, 64), (22, 64), (22, 63)]
  | 5, 0 => [(39, 62), (39, 60), (36, 60), (36, 48)]
  | 5, 1 => [(39, 62), (38, 62), (38, 63)]
  | 5, 2 => [(39, 62), (40, 62), (40, 63)]
  | 6, 0 => [(39, 64), (38, 64), (38, 63)]
  | 6, 1 => [(39, 64), (40, 64), (40, 63)]
  | 7, 0 => [(57, 62), (57, 60), (54, 60), (54, 48)]
  | 7, 1 => [(57, 62), (56, 62), (56, 63)]
  | 7, 2 => [(57, 62), (58, 62), (58, 63)]
  | 8, 0 => [(57, 64), (56, 64), (56, 63)]
  | 8, 1 => [(57, 64), (58, 64), (58, 63)]
  | _, _ => []

/-- Complete two-stage drawing for an empty source clause. -/
def zeroDrawing :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := zeroFormula
  variablePosition := variablePosition
  routes := zeroRoute

/-- The complete empty-source two-stage neighborhood is continuously
planar. -/
theorem zeroDrawing_isValid : zeroDrawing.IsValid := by
  native_decide

/-! ## Source-polarity-independent certificates -/

/-- Full-width composed formula with arbitrary source polarities. -/
def fullFormulaFor
    (first second third : Bool) :
    List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .sourceFirst, first),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .sourceSecond, !second),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .sourceThird, !third),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]]

/-- Full-width composed drawing with arbitrary source polarities. -/
def fullDrawingFor
    (first second third : Bool) :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := fullFormulaFor first second third
  variablePosition := variablePosition
  routes := fullRoute

/-- The full-width geometry is valid for every source-polarity pattern. -/
theorem fullDrawingFor_isValid
    (first second third : Bool) :
    (fullDrawingFor first second third).IsValid := by
  cases first <;> cases second <;> cases third <;>
    native_decide

/-- Binary-source composed formula with arbitrary present-source
polarities. -/
def twoFormulaFor
    (first second : Bool) :
    List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .sourceFirst, first),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .sourceSecond, !second),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .thirdPadding, false),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]] ++
    forcedFalseUnitReplacement 3 .thirdPadding

/-- Binary-source composed drawing with arbitrary present-source
polarities. -/
def twoDrawingFor
    (first second : Bool) :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := twoFormulaFor first second
  variablePosition := variablePosition
  routes := twoRoute

/-- The binary-source geometry is valid for every source-polarity pattern. -/
theorem twoDrawingFor_isValid
    (first second : Bool) :
    (twoDrawingFor first second).IsValid := by
  cases first <;> cases second <;> native_decide

/-- Unit-source composed formula with arbitrary source polarity. -/
def oneFormulaFor
    (first : Bool) :
    List (EmbeddedClause FigureNineNoUnitsVariable) :=
  [clause (39, 15)
      [(.inherited .sourceFirst, first),
        (.inherited .firstChoice, true),
        (.inherited .secondChoice, true)],
    clause (21, 33)
      [(.inherited .secondPadding, false),
        (.inherited .firstChoice, true),
        (.inherited .firstSlack, true)],
    clause (57, 33)
      [(.inherited .thirdPadding, false),
        (.inherited .secondChoice, true),
        (.inherited .secondSlack, true)]] ++
    forcedFalseUnitReplacement 3 .secondPadding ++
    forcedFalseUnitReplacement 4 .thirdPadding

/-- Unit-source composed drawing with arbitrary source polarity. -/
def oneDrawingFor
    (first : Bool) :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable where
  formula := oneFormulaFor first
  variablePosition := variablePosition
  routes := oneRoute

/-- The unit-source geometry is valid for either source polarity. -/
theorem oneDrawingFor_isValid
    (first : Bool) :
    (oneDrawingFor first).IsValid := by
  cases first <;> native_decide

@[simp]
theorem fullFormulaFor_true :
    fullFormulaFor true true true = fullFormula := rfl

@[simp]
theorem twoFormulaFor_true :
    twoFormulaFor true true = twoFormula := rfl

@[simp]
theorem oneFormulaFor_true :
    oneFormulaFor true = oneFormula := rfl

/-! ## Correspondence with the composed positioned transformation -/

/-- Regard a Figure 9 embedded clause as a positioned periodic clause whose
literal offsets are all zero. -/
def positionFigureNineClause
    {Variable : Type*}
    (source : EmbeddedClause Variable) :
    PositionedPeriodicClause Variable where
  position := source.position
  literals := source.literals.map fun literal =>
    ⟨literal.1, (0, 0), literal.2⟩

/-- Forget the nested scopes introduced by the two transformations while
remembering exactly which finite combined role each output variable has. -/
def composedOutputRole :
    OneInThreeNoUnitVariable
        (OneInThreeVariable
          PlanarOneInThree.FigureNineSourceVariable) →
      FigureNineNoUnitsVariable
  | .inl source =>
      .inherited
        (PlanarOneInThree.figureNineOutputRole source)
  | .inr ((sourceClauseIndex, _), kind) =>
      .unitAux sourceClauseIndex kind

/-- Run Figure 9 and then positioned unit elimination on one canonical
source clause, forget only logical offsets, and rename nested scopes to the
finite combined roles. -/
def generatedComposedTemplateFor
    (literals :
      List
        (PlanarOneInThree.FigureNineSourceVariable × Bool)) :
    List (EmbeddedClause FigureNineNoUnitsVariable) :=
  let figureNine :=
    PlanarOneInThree.clauseGadget 0
      (PlanarOneInThree.canonicalFigureNineSourceFor literals)
  figureNine.zipIdx.flatMap fun taggedClause =>
    (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
      taggedClause.2
      (positionFigureNineClause taggedClause.1)).map fun generated =>
        (PlanarOneInThreeNoUnits.embedPositionedClause
          generated).rename composedOutputRole

/-- The arbitrary-polarity full template is exactly Figure 9 followed by
positioned unit elimination. -/
theorem generatedComposedTemplateFor_three
    (first second third : Bool) :
    generatedComposedTemplateFor
        [(.first, first), (.second, second), (.third, third)] =
      fullFormulaFor first second third := by
  cases first <;> cases second <;> cases third <;>
    native_decide

/-- The arbitrary-polarity binary template is exactly the corresponding
two-stage positioned transformation. -/
theorem generatedComposedTemplateFor_two
    (first second : Bool) :
    generatedComposedTemplateFor
        [(.first, first), (.second, second)] =
      twoFormulaFor first second := by
  cases first <;> cases second <;> native_decide

/-- The arbitrary-polarity unit template is exactly the corresponding
two-stage positioned transformation. -/
theorem generatedComposedTemplateFor_one
    (first : Bool) :
    generatedComposedTemplateFor [(.first, first)] =
      oneFormulaFor first := by
  cases first <;> native_decide

/-- The empty template is exactly the corresponding two-stage positioned
transformation. -/
theorem generatedComposedTemplateFor_zero :
    generatedComposedTemplateFor [] = zeroFormula := by
  native_decide

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

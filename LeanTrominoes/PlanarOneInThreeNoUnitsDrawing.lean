/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicCNFPlanarOneInThreePlacements

/-!
# Certified local drawings for exact-one unit elimination

`PeriodicOneInThreeNoUnits` replaces an empty exact-one clause by an
unsatisfiable triangle and a unit clause by a two-clause diamond.  Clauses of
arity two or three are retained.  This file supplies exact finite geometric
certificates for all four local cases in the established `6 × 6` refinement
cell.

Present source variables are represented by boundary ports.  The auxiliary
variables and generated clauses use the coordinates already chosen by
`PeriodicOneInThreeNoUnitsPositioned`.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnits

open PlanarThreeSAT

/-- Variables visible in one unit-elimination neighborhood. -/
inductive UnitEliminationVariable
  | sourceFirst
  | sourceSecond
  | sourceThird
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- Source incidences use top, left, and right boundary ports; auxiliaries
occupy their established local vertices. -/
def variablePosition : UnitEliminationVariable → Cell
  | .sourceFirst => (3, 0)
  | .sourceSecond => (0, 3)
  | .sourceThird => (6, 3)
  | .first =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition .first
  | .second =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition .second
  | .third =>
      PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition .third

/-- One generated exact-one clause at a local unit-elimination position. -/
def clause
    (position : Cell)
    (literals : List (UnitEliminationVariable × Bool)) :
    EmbeddedClause UnitEliminationVariable where
  position := position
  literals := literals

/-! ## Empty source clause -/

/-- The three binary clauses of the unsatisfiable empty-clause triangle. -/
def emptyFormula : List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 1) [(.first, true), (.second, true)],
    clause (5, 4) [(.second, true), (.third, true)],
    clause (1, 4) [(.first, true), (.third, true)]]

/-- Explicit routes around the empty-clause triangle. -/
def emptyRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(3, 1), (2, 1), (2, 3)]
  | 0, 1 => [(3, 1), (4, 1), (4, 3)]
  | 1, 0 => [(5, 4), (5, 3), (4, 3)]
  | 1, 1 => [(5, 4), (5, 5), (3, 5)]
  | 2, 0 => [(1, 4), (1, 3), (2, 3)]
  | 2, 1 => [(1, 4), (1, 5), (3, 5)]
  | _, _ => []

/-- Complete drawing of the empty-clause triangle. -/
def emptyDrawing :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := emptyFormula
  variablePosition := variablePosition
  routes := emptyRoute

/-- The empty-clause triangle is a valid continuous orthogonal drawing. -/
theorem emptyDrawing_isValid : emptyDrawing.IsValid := by
  native_decide

/-! ## Unit source clause -/

/-- The two-clause diamond replacing a unit exact-one clause. -/
def unitFormula : List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 2)
      [(.sourceFirst, false), (.first, true), (.second, true)],
    clause (3, 4) [(.first, true), (.second, true)]]

/-- Explicit routes around the unit-clause diamond. -/
def unitRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(3, 2), (3, 0)]
  | 0, 1 => [(3, 2), (2, 2), (2, 3)]
  | 0, 2 => [(3, 2), (4, 2), (4, 3)]
  | 1, 0 => [(3, 4), (2, 4), (2, 3)]
  | 1, 1 => [(3, 4), (4, 4), (4, 3)]
  | _, _ => []

/-- Complete drawing of the unit-clause diamond. -/
def unitDrawing :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := unitFormula
  variablePosition := variablePosition
  routes := unitRoute

/-- The unit-clause diamond is a valid continuous orthogonal drawing. -/
theorem unitDrawing_isValid : unitDrawing.IsValid := by
  native_decide

/-! ## Retained source clauses -/

/-- A retained binary exact-one clause at the central generated position. -/
def twoFormula : List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 3) [(.sourceFirst, true), (.sourceSecond, true)]]

/-- The two retained incidences leave through distinct boundary ports. -/
def twoRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(3, 3), (3, 0)]
  | 0, 1 => [(3, 3), (0, 3)]
  | _, _ => []

/-- Complete drawing of a retained binary exact-one clause. -/
def twoDrawing :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := twoFormula
  variablePosition := variablePosition
  routes := twoRoute

/-- A retained binary clause is a valid continuous orthogonal drawing. -/
theorem twoDrawing_isValid : twoDrawing.IsValid := by
  native_decide

/-- A retained ternary exact-one clause at the central generated position. -/
def threeFormula : List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 3)
      [(.sourceFirst, true), (.sourceSecond, true),
        (.sourceThird, true)]]

/-- The three retained incidences leave through distinct boundary ports. -/
def threeRoute (clauseIndex literalIndex : Nat) : List Cell :=
  match clauseIndex, literalIndex with
  | 0, 0 => [(3, 3), (3, 0)]
  | 0, 1 => [(3, 3), (0, 3)]
  | 0, 2 => [(3, 3), (6, 3)]
  | _, _ => []

/-- Complete drawing of a retained ternary exact-one clause. -/
def threeDrawing :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := threeFormula
  variablePosition := variablePosition
  routes := threeRoute

/-- A retained ternary clause is a valid continuous orthogonal drawing. -/
theorem threeDrawing_isValid : threeDrawing.IsValid := by
  native_decide

/-! ## Source-polarity-independent certificates -/

/-- The unit diamond with arbitrary source literal polarity.  Its ternary
replacement clause contains the negated source literal. -/
def unitFormulaFor
    (polarity : Bool) :
    List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 2)
      [(.sourceFirst, !polarity), (.first, true), (.second, true)],
    clause (3, 4) [(.first, true), (.second, true)]]

/-- Unit-clause diamond with arbitrary source literal polarity. -/
def unitDrawingFor
    (polarity : Bool) :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := unitFormulaFor polarity
  variablePosition := variablePosition
  routes := unitRoute

/-- The unit diamond is geometrically valid for either source polarity. -/
theorem unitDrawingFor_isValid
    (polarity : Bool) :
    (unitDrawingFor polarity).IsValid := by
  cases polarity <;> native_decide

/-- A retained binary clause with arbitrary literal polarities. -/
def twoFormulaFor
    (first second : Bool) :
    List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 3)
      [(.sourceFirst, first), (.sourceSecond, second)]]

/-- Retained binary drawing with arbitrary literal polarities. -/
def twoDrawingFor
    (first second : Bool) :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := twoFormulaFor first second
  variablePosition := variablePosition
  routes := twoRoute

/-- The retained binary drawing is valid for every polarity pattern. -/
theorem twoDrawingFor_isValid
    (first second : Bool) :
    (twoDrawingFor first second).IsValid := by
  cases first <;> cases second <;> native_decide

/-- A retained ternary clause with arbitrary literal polarities. -/
def threeFormulaFor
    (first second third : Bool) :
    List (EmbeddedClause UnitEliminationVariable) :=
  [clause (3, 3)
      [(.sourceFirst, first), (.sourceSecond, second),
        (.sourceThird, third)]]

/-- Retained ternary drawing with arbitrary literal polarities. -/
def threeDrawingFor
    (first second third : Bool) :
    EmbeddedCNFIncidenceDrawing UnitEliminationVariable where
  formula := threeFormulaFor first second third
  variablePosition := variablePosition
  routes := threeRoute

/-- The retained ternary drawing is valid for every polarity pattern. -/
theorem threeDrawingFor_isValid
    (first second third : Bool) :
    (threeDrawingFor first second third).IsValid := by
  cases first <;> cases second <;> cases third <;>
    native_decide

@[simp]
theorem unitFormulaFor_true :
    unitFormulaFor true = unitFormula := rfl

@[simp]
theorem twoFormulaFor_true :
    twoFormulaFor true true = twoFormula := rfl

@[simp]
theorem threeFormulaFor_true :
    threeFormulaFor true true true = threeFormula := rfl

/-! ## Correspondence with the positioned unit-elimination transformation -/

/-- Canonical source-variable roles used to compare the finite templates
with `PeriodicOneInThreeNoUnitsPositioned.clauseGadget`. -/
inductive UnitEliminationSourceVariable
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- Rename the actual scoped output variables of a canonical unit-elimination
replacement to their finite drawing roles. -/
def outputRole :
    OneInThreeNoUnitVariable UnitEliminationSourceVariable →
      UnitEliminationVariable
  | .inl .first => .sourceFirst
  | .inl .second => .sourceSecond
  | .inl .third => .sourceThird
  | .inr (_, .first) => .first
  | .inr (_, .second) => .second
  | .inr (_, .third) => .third

/-- A canonical positioned periodic clause at the origin with positive,
zero-offset literals in the given role order. -/
def canonicalSource
    (roles : List UnitEliminationSourceVariable) :
    PositionedPeriodicClause UnitEliminationSourceVariable where
  position := (0, 0)
  literals := roles.map fun role =>
    ⟨role, (0, 0), true⟩

/-- Forget only the periodic literal offsets of a positioned clause. -/
def embedPositionedClause {Variable : Type*}
    (source : PositionedPeriodicClause Variable) :
    EmbeddedClause Variable where
  position := source.position
  literals := source.literals.map fun literal =>
    (literal.atom, literal.value)

/-- Run the actual positioned unit-elimination replacement, forget logical
offsets, and rename its scoped variables to finite local roles. -/
def generatedTemplate
    (roles : List UnitEliminationSourceVariable) :
    List (EmbeddedClause UnitEliminationVariable) :=
  (PeriodicOneInThreeNoUnitsPositioned.clauseGadget 0
    (canonicalSource roles)).map fun generated =>
      (embedPositionedClause generated).rename outputRole

/-- A canonical positioned source clause whose role and polarity are both
explicit. -/
def canonicalSourceFor
    (literals :
      List (UnitEliminationSourceVariable × Bool)) :
    PositionedPeriodicClause UnitEliminationSourceVariable where
  position := (0, 0)
  literals := literals.map fun literal =>
    ⟨literal.1, (0, 0), literal.2⟩

/-- Actual positioned unit-elimination output for explicit canonical source
polarities, embedded and renamed to the finite drawing roles. -/
def generatedTemplateFor
    (literals :
      List (UnitEliminationSourceVariable × Bool)) :
    List (EmbeddedClause UnitEliminationVariable) :=
  (PeriodicOneInThreeNoUnitsPositioned.clauseGadget 0
    (canonicalSourceFor literals)).map fun generated =>
      (embedPositionedClause generated).rename outputRole

/-- The empty finite template is exactly the positioned empty-clause
replacement. -/
theorem generatedTemplate_zero :
    generatedTemplate [] = emptyFormula := by
  native_decide

/-- The unit finite template is exactly the positioned unit-clause
replacement. -/
theorem generatedTemplate_one :
    generatedTemplate [.first] = unitFormula := by
  native_decide

/-- The binary finite template is exactly the retained positioned binary
clause. -/
theorem generatedTemplate_two :
    generatedTemplate [.first, .second] = twoFormula := by
  native_decide

/-- The ternary finite template is exactly the retained positioned ternary
clause. -/
theorem generatedTemplate_three :
    generatedTemplate [.first, .second, .third] =
      threeFormula := by
  native_decide

/-- The arbitrary-polarity unit template is exactly the corresponding
positioned unit-elimination output. -/
theorem generatedTemplateFor_one
    (polarity : Bool) :
    generatedTemplateFor [(.first, polarity)] =
      unitFormulaFor polarity := by
  cases polarity <;> native_decide

/-- The arbitrary-polarity binary template is exactly the retained
positioned source clause. -/
theorem generatedTemplateFor_two
    (first second : Bool) :
    generatedTemplateFor
        [(.first, first), (.second, second)] =
      twoFormulaFor first second := by
  cases first <;> cases second <;> native_decide

/-- The arbitrary-polarity ternary template is exactly the retained
positioned source clause. -/
theorem generatedTemplateFor_three
    (first second third : Bool) :
    generatedTemplateFor
        [(.first, first), (.second, second), (.third, third)] =
      threeFormulaFor first second third := by
  cases first <;> cases second <;> cases third <;>
    native_decide

end PlanarOneInThreeNoUnits
end LeanTrominoes

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

end PlanarOneInThreeNoUnits
end LeanTrominoes

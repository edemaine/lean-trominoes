import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PlanarOneInThreeFigureNineDrawing

/-!
# Instantiating the certified Figure 9 drawings

The finite Figure 9 templates use role names and local coordinates.  This
file renames the full-width template to the actual source atoms and
clause-scoped `OneInThreeVariable` auxiliaries, then translates it into an
arbitrary positioned source-clause macrocell.
-/

namespace LeanTrominoes
namespace PlanarOneInThree

open PlanarThreeSAT

/-- A ternary source clause used by the full-width instantiated drawing. -/
def threeSourceClause {Variable : Type*}
    (position : Cell)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (third : Variable) (thirdPolarity : Bool) :
    EmbeddedClause Variable where
  position := position
  literals :=
    [(first, firstPolarity),
      (second, secondPolarity),
      (third, thirdPolarity)]

/-- Rename every finite full-width role to its actual source atom or scoped
Figure 9 auxiliary. -/
def threeVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first second third : Variable) :
    FigureNineVariable → OneInThreeVariable Variable
  | .sourceFirst => .inl first
  | .sourceSecond => .inl second
  | .sourceThird => .inl third
  | .firstChoice =>
      .inr ((clauseIndex, zeroOffsetClause source), .firstChoice)
  | .secondChoice =>
      .inr ((clauseIndex, zeroOffsetClause source), .secondChoice)
  | .firstSlack =>
      .inr ((clauseIndex, zeroOffsetClause source), .firstSlack)
  | .secondSlack =>
      .inr ((clauseIndex, zeroOffsetClause source), .secondSlack)
  | .firstPadding =>
      .inr ((clauseIndex, zeroOffsetClause source), .firstPadding)
  | .secondPadding =>
      .inr ((clauseIndex, zeroOffsetClause source), .secondPadding)
  | .thirdPadding =>
      .inr ((clauseIndex, zeroOffsetClause source), .thirdPadding)

/-- Pull the actual output-variable names back to the full-width template's
local port and auxiliary coordinates. -/
def threeLocalPosition {Variable : Type*} [DecidableEq Variable]
    (first second third : Variable) :
    OneInThreeVariable Variable → Cell
  | .inl atom =>
      if atom = first then (6, 0)
      else if atom = second then (0, 5)
      else if atom = third then (12, 5)
      else (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition kind

/-- The certified full-width Figure 9 drawing instantiated at one arbitrary
positioned ternary source clause. -/
def instantiatedThreeDrawing {Variable : Type*}
    [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (third : Variable) (thirdPolarity : Bool) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let source :=
    threeSourceClause position
      first firstPolarity second secondPolarity
      third thirdPolarity
  ((figureNineDrawingFor
      firstPolarity secondPolarity thirdPolarity).rename
    (threeVariableMap clauseIndex source first second third)
    (threeLocalPosition first second third)).translate
      (Cell.scale gadgetScale position)

/-- The instantiated drawing's formula is exactly the actual positioned
Figure 9 clause gadget. -/
theorem instantiatedThreeDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (third : Variable) (thirdPolarity : Bool) :
    (instantiatedThreeDrawing position clauseIndex
      first firstPolarity second secondPolarity
      third thirdPolarity).formula =
    clauseGadget clauseIndex
      (threeSourceClause position
        first firstPolarity second secondPolarity
        third thirdPolarity) := by
  rfl

/-- Pairwise distinct source atoms make the full role renaming injective. -/
theorem threeVariableMap_injective
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first second third : Variable)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third) :
    Function.Injective
      (threeVariableMap clauseIndex source
        first second third) := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [threeVariableMap]

/-- Every role renamed by the full-width instance retains its local
coordinate. -/
theorem threeLocalPosition_map
    {Variable : Type*} [DecidableEq Variable]
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first second third : Variable)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third)
    (role : FigureNineVariable) :
    threeLocalPosition first second third
        (threeVariableMap clauseIndex source
          first second third role) =
      figureNineVariablePosition role := by
  cases role <;>
    simp [threeLocalPosition, threeVariableMap,
      figureNineVariablePosition,
      Ne.symm firstNeSecond, Ne.symm firstNeThird,
      Ne.symm secondNeThird]

/-- Every full-width Figure 9 instance inherits the exact endpoint,
orthogonality, and continuous-planarity certificate. -/
theorem instantiatedThreeDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (third : Variable) (thirdPolarity : Bool)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third) :
    (instantiatedThreeDrawing position clauseIndex
      first firstPolarity second secondPolarity
      third thirdPolarity).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left _leftMember right _rightMember equal
    exact threeVariableMap_injective
      clauseIndex
      (threeSourceClause position
        first firstPolarity second secondPolarity
        third thirdPolarity)
      first second third
      firstNeSecond firstNeThird secondNeThird equal
  · intro role _roleMember
    exact threeLocalPosition_map
      clauseIndex
      (threeSourceClause position
        first firstPolarity second secondPolarity
        third thirdPolarity)
      first second third
      firstNeSecond firstNeThird secondNeThird role
  · exact figureNineDrawingFor_isValid
      firstPolarity secondPolarity thirdPolarity

end PlanarOneInThree
end LeanTrominoes

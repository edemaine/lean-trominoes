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

/-! ## Binary source clauses -/

/-- A positioned binary source clause. -/
def twoSourceClause {Variable : Type*}
    (position : Cell)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool) :
    EmbeddedClause Variable where
  position := position
  literals :=
    [(first, firstPolarity), (second, secondPolarity)]

/-- Rename the occurring roles of the padded binary template.  The unused
third source role may harmlessly reuse the first atom. -/
def twoVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first second : Variable) :
    FigureNineVariable → OneInThreeVariable Variable
  | .sourceFirst => .inl first
  | .sourceSecond => .inl second
  | .sourceThird => .inl first
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

/-- Local target placement for the two present source ports and every
Figure 9 auxiliary role. -/
def twoLocalPosition {Variable : Type*} [DecidableEq Variable]
    (first second : Variable) :
    OneInThreeVariable Variable → Cell
  | .inl atom =>
      if atom = first then (6, 0)
      else if atom = second then (0, 5)
      else (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition kind

/-- Certified padded binary Figure 9 drawing at an arbitrary source
position. -/
def instantiatedTwoDrawing {Variable : Type*}
    [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let source :=
    twoSourceClause position
      first firstPolarity second secondPolarity
  ((figureNineTwoDrawingFor
      firstPolarity secondPolarity).rename
    (twoVariableMap clauseIndex source first second)
    (twoLocalPosition first second)).translate
      (Cell.scale gadgetScale position)

theorem instantiatedTwoDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool) :
    (instantiatedTwoDrawing position clauseIndex
      first firstPolarity second secondPolarity).formula =
    clauseGadget clauseIndex
      (twoSourceClause position
        first firstPolarity second secondPolarity) := by
  rfl

/-- The binary role map is injective on the variables that actually occur
when the two source atoms are distinct. -/
theorem twoVariableMap_injectiveOn
    {Variable : Type*}
    (firstPolarity secondPolarity : Bool)
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first second : Variable)
    (firstNeSecond : first ≠ second) :
    ∀ left ∈
        (figureNineTwoDrawingFor
          firstPolarity secondPolarity).variableVertices,
      ∀ right ∈
        (figureNineTwoDrawingFor
          firstPolarity secondPolarity).variableVertices,
        twoVariableMap clauseIndex source first second left =
            twoVariableMap clauseIndex source first second right →
          left = right := by
  intro left leftMember right rightMember equal
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    figureNineTwoDrawingFor, figureNineTwoFormulaFor,
    figureNineClause] at leftMember rightMember
  cases left <;> cases right <;>
    simp_all [twoVariableMap]

/-- Every occurring binary-template role retains its local coordinate. -/
theorem twoLocalPosition_map
    {Variable : Type*} [DecidableEq Variable]
    (firstPolarity secondPolarity : Bool)
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first second : Variable)
    (firstNeSecond : first ≠ second) :
    ∀ role ∈
        (figureNineTwoDrawingFor
          firstPolarity secondPolarity).variableVertices,
      twoLocalPosition first second
          (twoVariableMap clauseIndex source
            first second role) =
        figureNineVariablePosition role := by
  intro role roleMember
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    figureNineTwoDrawingFor, figureNineTwoFormulaFor,
    figureNineClause] at roleMember
  cases role <;>
    simp_all [twoLocalPosition, twoVariableMap,
      figureNineVariablePosition, Ne.symm firstNeSecond]

theorem instantiatedTwoDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool)
    (second : Variable) (secondPolarity : Bool)
    (firstNeSecond : first ≠ second) :
    (instantiatedTwoDrawing position clauseIndex
      first firstPolarity second secondPolarity).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · simpa [figureNineTwoDrawingFor,
      figureNineTwoFormulaFor] using
      twoVariableMap_injectiveOn
        firstPolarity secondPolarity clauseIndex
        (twoSourceClause position
          first firstPolarity second secondPolarity)
        first second firstNeSecond
  · simpa [figureNineTwoDrawingFor,
      figureNineTwoFormulaFor] using
      twoLocalPosition_map
        firstPolarity secondPolarity clauseIndex
        (twoSourceClause position
          first firstPolarity second secondPolarity)
        first second firstNeSecond
  · exact figureNineTwoDrawingFor_isValid
      firstPolarity secondPolarity

/-! ## Unit source clauses -/

def oneSourceClause {Variable : Type*}
    (position : Cell)
    (first : Variable) (firstPolarity : Bool) :
    EmbeddedClause Variable where
  position := position
  literals := [(first, firstPolarity)]

/-- Rename the occurring roles of the padded unit template. -/
def oneVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable)
    (first : Variable) :
    FigureNineVariable → OneInThreeVariable Variable
  | .sourceFirst | .sourceSecond | .sourceThird => .inl first
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

def oneLocalPosition {Variable : Type*} [DecidableEq Variable]
    (first : Variable) :
    OneInThreeVariable Variable → Cell
  | .inl atom => if atom = first then (6, 0) else (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition kind

def instantiatedOneDrawing {Variable : Type*}
    [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let source :=
    oneSourceClause position first firstPolarity
  ((figureNineOneDrawingFor firstPolarity).rename
    (oneVariableMap clauseIndex source first)
    (oneLocalPosition first)).translate
      (Cell.scale gadgetScale position)

theorem instantiatedOneDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool) :
    (instantiatedOneDrawing position clauseIndex
      first firstPolarity).formula =
    clauseGadget clauseIndex
      (oneSourceClause position first firstPolarity) := by
  rfl

theorem instantiatedOneDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat)
    (first : Variable) (firstPolarity : Bool) :
    (instantiatedOneDrawing position clauseIndex
      first firstPolarity).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left leftMember right rightMember equal
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      figureNineOneDrawingFor, figureNineOneFormulaFor,
      figureNineClause] at leftMember rightMember
    cases left <;> cases right <;>
      simp_all [oneVariableMap]
  · intro role roleMember
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      figureNineOneDrawingFor, figureNineOneFormulaFor,
      figureNineClause] at roleMember
    cases role <;>
      simp_all [oneLocalPosition, oneVariableMap,
        figureNineOneDrawingFor,
        figureNineVariablePosition]
  · exact figureNineOneDrawingFor_isValid firstPolarity

/-! ## Empty source clauses -/

def zeroSourceClause {Variable : Type*}
    (position : Cell) : EmbeddedClause Variable where
  position := position
  literals := []

/-- Rename the auxiliary roles of the padded empty template.  Its absent
source roles receive an arbitrary auxiliary name that never occurs. -/
def zeroVariableMap {Variable : Type*}
    (clauseIndex : Nat)
    (source : EmbeddedClause Variable) :
    FigureNineVariable → OneInThreeVariable Variable
  | .sourceFirst | .sourceSecond | .sourceThird =>
      .inr ((clauseIndex, zeroOffsetClause source), .firstChoice)
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

def zeroLocalPosition {Variable : Type*} :
    OneInThreeVariable Variable → Cell
  | .inl _ => (0, 0)
  | .inr (_, kind) =>
      PeriodicOneInThreePositioned.auxiliaryLocalPosition kind

def instantiatedZeroDrawing {Variable : Type*}
    [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeVariable Variable) :=
  let source := zeroSourceClause (Variable := Variable) position
  (figureNineZeroDrawing.rename
    (zeroVariableMap clauseIndex source)
    zeroLocalPosition).translate
      (Cell.scale gadgetScale position)

theorem instantiatedZeroDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat) :
    (instantiatedZeroDrawing (Variable := Variable)
      position clauseIndex).formula =
    clauseGadget clauseIndex
      (zeroSourceClause (Variable := Variable) position) := by
  rfl

theorem instantiatedZeroDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (position : Cell) (clauseIndex : Nat) :
    (instantiatedZeroDrawing (Variable := Variable)
      position clauseIndex).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro left leftMember right rightMember equal
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      figureNineZeroDrawing, figureNineZeroFormula,
      figureNineClause] at leftMember rightMember
    cases left <;> cases right <;>
      simp_all [zeroVariableMap]
  · intro role roleMember
    simp [EmbeddedCNFIncidenceDrawing.variableVertices,
      figureNineZeroDrawing, figureNineZeroFormula,
      figureNineClause] at roleMember
    cases role <;>
      simp_all [zeroLocalPosition, zeroVariableMap,
        figureNineZeroDrawing,
        figureNineVariablePosition]
  · exact figureNineZeroDrawing_isValid

end PlanarOneInThree
end LeanTrominoes

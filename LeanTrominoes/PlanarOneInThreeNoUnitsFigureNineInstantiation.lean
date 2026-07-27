import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineDrawing

/-!
# Instantiating the composed Figure 9 and unit-elimination drawings

The composed finite templates use role names and start at the origin.  This
file renames those roles to the two nested variable types introduced by the
actual reductions, and translates the routes into an arbitrary source-clause
macrocell.

The second reduction numbers its source clauses in the flattened Figure 9
formula.  Consequently an instance also receives the global presentation
index of the first Figure 9 clause in its local block.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Explicit equality decision for the two nested reduction-variable layers.
Unfolding both abbreviations avoids an instance-synthesis loop through their
clause scopes. -/
def nestedVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) := by
  letI : DecidableEq (OneInThreeVariable Variable) :=
    inferInstance
  letI :
      DecidableEq
        (PeriodicLiteral (OneInThreeVariable Variable)) :=
    inferInstance
  letI :
      DecidableEq
        (PeriodicClause (OneInThreeVariable Variable)) :=
    List.hasDecEq
  unfold OneInThreeNoUnitVariable
  infer_instance

/-- Combined refinement scale of Figure 9 followed by unit elimination. -/
def composedGadgetScale : Int :=
  PlanarOneInThree.gadgetScale *
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale

/-- Literal list of one actual positioned Figure 9 clause, with a harmless
default outside the local block. -/
def figureNineClauseLiterals
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (localClauseIndex : Nat) :
    PeriodicClause (OneInThreeVariable Variable) :=
  (((PeriodicOneInThreePositioned.clauseGadget
      sourceClauseIndex source)[localClauseIndex]?).map
        PositionedPeriodicClause.literals).getD []

/-- Lift a finite combined role through an actual first-stage variable map
and give second-stage auxiliaries their global Figure 9 clause scope. -/
def variableMap
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (inheritedMap :
      PlanarOneInThree.FigureNineVariable →
        OneInThreeVariable Variable) :
    FigureNineNoUnitsVariable →
      OneInThreeNoUnitVariable (OneInThreeVariable Variable)
  | .inherited role => .inl (inheritedMap role)
  | .unitAux localClauseIndex kind =>
      .inr
        ((figureNineClauseStart + localClauseIndex,
          figureNineClauseLiterals
            sourceClauseIndex source localClauseIndex),
          kind)

/-- First-stage variable map for a genuine ternary source clause. -/
def threeInheritedMap
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : Variable) :
    PlanarOneInThree.FigureNineVariable →
      OneInThreeVariable Variable
  | .sourceFirst => .inl first
  | .sourceSecond => .inl second
  | .sourceThird => .inl third
  | .firstChoice =>
      .inr ((sourceClauseIndex, source.literals), .firstChoice)
  | .secondChoice =>
      .inr ((sourceClauseIndex, source.literals), .secondChoice)
  | .firstSlack =>
      .inr ((sourceClauseIndex, source.literals), .firstSlack)
  | .secondSlack =>
      .inr ((sourceClauseIndex, source.literals), .secondSlack)
  | .firstPadding =>
      .inr ((sourceClauseIndex, source.literals), .firstPadding)
  | .secondPadding =>
      .inr ((sourceClauseIndex, source.literals), .secondPadding)
  | .thirdPadding =>
      .inr ((sourceClauseIndex, source.literals), .thirdPadding)

/-- Complete two-stage variable map for a ternary source clause. -/
def threeVariableMap
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : Variable) :
    FigureNineNoUnitsVariable →
      OneInThreeNoUnitVariable (OneInThreeVariable Variable) :=
  variableMap sourceClauseIndex figureNineClauseStart source
    (threeInheritedMap sourceClauseIndex source
      first second third)

/-- Certified composed drawing instantiated at an arbitrary ternary
positioned source clause. -/
def instantiatedThreeDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  letI := nestedVariableDecidableEq (Variable := Variable)
  (EmbeddedCNFIncidenceDrawing.renameToImage
    (fullDrawingFor
      first.value second.value third.value)
    (threeVariableMap
      sourceClauseIndex figureNineClauseStart source
      first.atom second.atom third.atom)).translate
        (Cell.scale composedGadgetScale source.position)

/-- Pairwise distinct source atoms make the composed ternary variable map
injective on every role that occurs in the finite drawing. -/
theorem threeVariableMap_injectiveOn
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom)
    (firstNeThird : first.atom ≠ third.atom)
    (secondNeThird : second.atom ≠ third.atom) :
    ∀ left ∈
        (fullDrawingFor
          first.value second.value third.value).variableVertices,
      ∀ right ∈
        (fullDrawingFor
          first.value second.value third.value).variableVertices,
        threeVariableMap
            sourceClauseIndex figureNineClauseStart source
            first.atom second.atom third.atom left =
          threeVariableMap
            sourceClauseIndex figureNineClauseStart source
            first.atom second.atom third.atom right →
        left = right := by
  intro left leftMember right rightMember equal
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    fullDrawingFor, fullFormulaFor, clause]
    at leftMember rightMember
  cases left with
  | inherited leftRole =>
      cases right with
      | inherited rightRole =>
          cases leftRole <;> cases rightRole <;>
            simp_all [threeVariableMap, variableMap,
              threeInheritedMap]
      | unitAux rightIndex rightKind =>
          simp [threeVariableMap, variableMap] at equal
  | unitAux leftIndex leftKind =>
      simp at leftMember

/-- Every genuine ternary instance inherits the complete finite geometric
certificate. -/
theorem instantiatedThreeDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom)
    (firstNeThird : first.atom ≠ third.atom)
    (secondNeThird : second.atom ≠ third.atom) :
    @EmbeddedCNFIncidenceDrawing.IsValid
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
      nestedVariableDecidableEq
      (instantiatedThreeDrawing
        sourceClauseIndex figureNineClauseStart source
        first second third) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.renameToImage_isValid
  · exact threeVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source
      first second third
      firstNeSecond firstNeThird secondNeThird
  · exact fullDrawingFor_isValid
      first.value second.value third.value

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

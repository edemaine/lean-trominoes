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

/-- Actual local clause block obtained by running positioned Figure 9 and
then unit elimination, using the supplied global index for the first
Figure 9 clause. -/
def composedClauseGadget
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    List
      (EmbeddedClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) :=
  (PeriodicOneInThreePositioned.clauseGadget
    sourceClauseIndex source).zipIdx.flatMap fun taggedClause =>
      (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
        (figureNineClauseStart + taggedClause.2)
        taggedClause.1).map
          PlanarOneInThreeNoUnits.embedPositionedClause

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

/-- The instantiated ternary drawing's formula is exactly its actual
two-stage positioned clause block. -/
theorem instantiatedThreeDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (sourceLiterals :
      source.literals = [first, second, third]) :
    (instantiatedThreeDrawing
      sourceClauseIndex figureNineClauseStart source
      first second third).formula =
        composedClauseGadget
          sourceClauseIndex figureNineClauseStart source := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  simp [instantiatedThreeDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    fullDrawingFor, fullFormulaFor, clause,
    threeVariableMap, variableMap, threeInheritedMap,
    composedClauseGadget,
    PeriodicOneInThreePositioned.clauseGadget,
    PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThreeNoUnits.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.liftLiteral,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate,
    PlanarOneInThree.generatedClausePosition,
    composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    EmbeddedClause.rename, EmbeddedClause.map,
    EmbeddedClause.translate, Cell.add, Cell.scale]
  unfold
    PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition
  simp [PeriodicOneInThreeNoUnits.liftLiteral,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.scale]
  omega

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

/-- Canonical image renaming preserves the translated position of every
occurring finite role in a ternary composed drawing. -/
theorem instantiatedThreeDrawing_rolePosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second third : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom)
    (firstNeThird : first.atom ≠ third.atom)
    (secondNeThird : second.atom ≠ third.atom)
    (role : FigureNineNoUnitsVariable)
    (roleMember :
      role ∈
        (fullDrawingFor
          first.value second.value third.value).variableVertices) :
    (instantiatedThreeDrawing
      sourceClauseIndex figureNineClauseStart source
      first second third).variablePosition
        (threeVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom second.atom third.atom role) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        ((fullDrawingFor
          first.value second.value third.value).variablePosition role) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  change
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        (fullDrawingFor
          first.value second.value third.value)
        (threeVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom second.atom third.atom)
        (threeVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom second.atom third.atom role)) =
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      ((fullDrawingFor
        first.value second.value third.value).variablePosition role)
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
    (fullDrawingFor first.value second.value third.value)
    (threeVariableMap
      sourceClauseIndex figureNineClauseStart source
      first.atom second.atom third.atom)
    (threeVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source
      first second third
      firstNeSecond firstNeThird secondNeThird)
    role roleMember]

/-! ## Binary source clauses -/

/-- First-stage variable map for a binary source clause.  The unused third
source role may harmlessly reuse the first atom. -/
def twoInheritedMap
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : Variable) :
    PlanarOneInThree.FigureNineVariable →
      OneInThreeVariable Variable
  | .sourceFirst => .inl first
  | .sourceSecond => .inl second
  | .sourceThird => .inl first
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

/-- Complete two-stage variable map for a binary source clause. -/
def twoVariableMap
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : Variable) :
    FigureNineNoUnitsVariable →
      OneInThreeNoUnitVariable (OneInThreeVariable Variable) :=
  variableMap sourceClauseIndex figureNineClauseStart source
    (twoInheritedMap sourceClauseIndex source first second)

/-- Certified composed drawing instantiated at an arbitrary binary
positioned source clause. -/
def instantiatedTwoDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  letI := nestedVariableDecidableEq (Variable := Variable)
  (EmbeddedCNFIncidenceDrawing.renameToImage
    (twoDrawingFor first.value second.value)
    (twoVariableMap
      sourceClauseIndex figureNineClauseStart source
      first.atom second.atom)).translate
        (Cell.scale composedGadgetScale source.position)

/-- The instantiated binary drawing's formula is exactly its actual
two-stage positioned clause block. -/
theorem instantiatedTwoDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (sourceLiterals : source.literals = [first, second]) :
    (instantiatedTwoDrawing
      sourceClauseIndex figureNineClauseStart source
      first second).formula =
        composedClauseGadget
          sourceClauseIndex figureNineClauseStart source := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  simp [instantiatedTwoDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    twoDrawingFor, twoFormulaFor,
    forcedFalseUnitReplacement, clause,
    twoVariableMap, variableMap, twoInheritedMap,
    figureNineClauseLiterals,
    composedClauseGadget,
    PeriodicOneInThreePositioned.clauseGadget,
    PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThreeNoUnits.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.padding,
    PeriodicOneInThree.forcePaddingFalse,
    PeriodicOneInThree.liftLiteral,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate,
    PlanarOneInThree.generatedClausePosition,
    composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    EmbeddedClause.rename, EmbeddedClause.map,
    EmbeddedClause.translate, Cell.add, Cell.scale]
  unfold
    PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition
  simp [PeriodicOneInThreeNoUnits.liftLiteral,
    PeriodicOneInThreeNoUnits.auxiliary,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.scale]
  omega

/-- Distinct binary source atoms make the composed map injective on every
occurring finite role. -/
theorem twoVariableMap_injectiveOn
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom) :
    ∀ left ∈
        (twoDrawingFor
          first.value second.value).variableVertices,
      ∀ right ∈
        (twoDrawingFor
          first.value second.value).variableVertices,
        twoVariableMap
            sourceClauseIndex figureNineClauseStart source
            first.atom second.atom left =
          twoVariableMap
            sourceClauseIndex figureNineClauseStart source
            first.atom second.atom right →
        left = right := by
  intro left leftMember right rightMember equal
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    twoDrawingFor, twoFormulaFor, forcedFalseUnitReplacement,
    clause] at leftMember rightMember
  cases left with
  | inherited leftRole =>
      cases right with
      | inherited rightRole =>
          cases leftRole <;> cases rightRole <;>
            simp_all [twoVariableMap, variableMap,
              twoInheritedMap]
      | unitAux rightIndex rightKind =>
          simp [twoVariableMap, variableMap] at equal
  | unitAux leftIndex leftKind =>
      cases right with
      | inherited rightRole =>
          simp [twoVariableMap, variableMap] at equal
      | unitAux rightIndex rightKind =>
          cases leftKind <;> cases rightKind <;>
            simp_all [twoVariableMap, variableMap]

/-- Every genuine binary instance inherits the complete finite geometric
certificate. -/
theorem instantiatedTwoDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom) :
    @EmbeddedCNFIncidenceDrawing.IsValid
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
      nestedVariableDecidableEq
      (instantiatedTwoDrawing
        sourceClauseIndex figureNineClauseStart source
        first second) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.renameToImage_isValid
  · exact twoVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source
      first second firstNeSecond
  · exact twoDrawingFor_isValid first.value second.value

/-- Canonical image renaming preserves the translated position of every
occurring finite role in a binary composed drawing. -/
theorem instantiatedTwoDrawing_rolePosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first second : PeriodicLiteral Variable)
    (firstNeSecond : first.atom ≠ second.atom)
    (role : FigureNineNoUnitsVariable)
    (roleMember :
      role ∈
        (twoDrawingFor
          first.value second.value).variableVertices) :
    (instantiatedTwoDrawing
      sourceClauseIndex figureNineClauseStart source
      first second).variablePosition
        (twoVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom second.atom role) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        ((twoDrawingFor
          first.value second.value).variablePosition role) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  change
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        (twoDrawingFor first.value second.value)
        (twoVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom second.atom)
        (twoVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom second.atom role)) =
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      ((twoDrawingFor
        first.value second.value).variablePosition role)
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
    (twoDrawingFor first.value second.value)
    (twoVariableMap
      sourceClauseIndex figureNineClauseStart source
      first.atom second.atom)
    (twoVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source
      first second firstNeSecond)
    role roleMember]

/-! ## Unit source clauses -/

/-- First-stage variable map for a unit source clause.  Unused source roles
may reuse its sole atom. -/
def oneInheritedMap
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : Variable) :
    PlanarOneInThree.FigureNineVariable →
      OneInThreeVariable Variable
  | .sourceFirst | .sourceSecond | .sourceThird => .inl first
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

/-- Complete two-stage variable map for a unit source clause. -/
def oneVariableMap
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : Variable) :
    FigureNineNoUnitsVariable →
      OneInThreeNoUnitVariable (OneInThreeVariable Variable) :=
  variableMap sourceClauseIndex figureNineClauseStart source
    (oneInheritedMap sourceClauseIndex source first)

/-- Certified composed drawing instantiated at an arbitrary unit positioned
source clause. -/
def instantiatedOneDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  letI := nestedVariableDecidableEq (Variable := Variable)
  (EmbeddedCNFIncidenceDrawing.renameToImage
    (oneDrawingFor first.value)
    (oneVariableMap
      sourceClauseIndex figureNineClauseStart source
      first.atom)).translate
        (Cell.scale composedGadgetScale source.position)

/-- The instantiated unit drawing's formula is exactly its actual two-stage
positioned clause block. -/
theorem instantiatedOneDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable)
    (sourceLiterals : source.literals = [first]) :
    (instantiatedOneDrawing
      sourceClauseIndex figureNineClauseStart source first).formula =
        composedClauseGadget
          sourceClauseIndex figureNineClauseStart source := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  simp [instantiatedOneDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    oneDrawingFor, oneFormulaFor,
    forcedFalseUnitReplacement, clause,
    oneVariableMap, variableMap, oneInheritedMap,
    figureNineClauseLiterals,
    composedClauseGadget,
    PeriodicOneInThreePositioned.clauseGadget,
    PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThreeNoUnits.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.padding,
    PeriodicOneInThree.forcePaddingFalse,
    PeriodicOneInThree.liftLiteral,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate,
    PlanarOneInThree.generatedClausePosition,
    composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    EmbeddedClause.rename, EmbeddedClause.map,
    EmbeddedClause.translate, Cell.add, Cell.scale]
  unfold
    PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition
  simp [PeriodicOneInThreeNoUnits.liftLiteral,
    PeriodicOneInThreeNoUnits.auxiliary,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.scale]
  omega

/-- The unit-source map is injective on every occurring finite role. -/
theorem oneVariableMap_injectiveOn
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    ∀ left ∈
        (oneDrawingFor first.value).variableVertices,
      ∀ right ∈
        (oneDrawingFor first.value).variableVertices,
        oneVariableMap
            sourceClauseIndex figureNineClauseStart source
            first.atom left =
          oneVariableMap
            sourceClauseIndex figureNineClauseStart source
            first.atom right →
        left = right := by
  intro left leftMember right rightMember equal
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    oneDrawingFor, oneFormulaFor, forcedFalseUnitReplacement,
    clause] at leftMember rightMember
  cases left with
  | inherited leftRole =>
      cases right with
      | inherited rightRole =>
          cases leftRole <;> cases rightRole <;>
            simp_all [oneVariableMap, variableMap,
              oneInheritedMap]
      | unitAux rightIndex rightKind =>
          simp [oneVariableMap, variableMap] at equal
  | unitAux leftIndex leftKind =>
      cases right with
      | inherited rightRole =>
          simp [oneVariableMap, variableMap] at equal
      | unitAux rightIndex rightKind =>
          cases leftKind <;> cases rightKind <;>
            simp_all [oneVariableMap, variableMap]

/-- Every genuine unit instance inherits the complete finite geometric
certificate. -/
theorem instantiatedOneDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable) :
    @EmbeddedCNFIncidenceDrawing.IsValid
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
      nestedVariableDecidableEq
      (instantiatedOneDrawing
        sourceClauseIndex figureNineClauseStart source first) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.renameToImage_isValid
  · exact oneVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source first
  · exact oneDrawingFor_isValid first.value

/-- Canonical image renaming preserves the translated position of every
occurring finite role in a unit-source composed drawing. -/
theorem instantiatedOneDrawing_rolePosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (first : PeriodicLiteral Variable)
    (role : FigureNineNoUnitsVariable)
    (roleMember :
      role ∈
        (oneDrawingFor first.value).variableVertices) :
    (instantiatedOneDrawing
      sourceClauseIndex figureNineClauseStart source
      first).variablePosition
        (oneVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom role) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        ((oneDrawingFor first.value).variablePosition role) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  change
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        (oneDrawingFor first.value)
        (oneVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom)
        (oneVariableMap
          sourceClauseIndex figureNineClauseStart source
          first.atom role)) =
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      ((oneDrawingFor first.value).variablePosition role)
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
    (oneDrawingFor first.value)
    (oneVariableMap
      sourceClauseIndex figureNineClauseStart source
      first.atom)
    (oneVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source first)
    role roleMember]

/-! ## Empty source clauses -/

/-- First-stage variable map for an empty source clause.  Absent source roles
receive a harmless auxiliary name that does not occur in the finite drawing. -/
def zeroInheritedMap
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (source : PositionedPeriodicClause Variable) :
    PlanarOneInThree.FigureNineVariable →
      OneInThreeVariable Variable
  | .sourceFirst | .sourceSecond | .sourceThird =>
      .inr ((sourceClauseIndex, source.literals), .firstChoice)
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

/-- Complete two-stage variable map for an empty source clause. -/
def zeroVariableMap
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    FigureNineNoUnitsVariable →
      OneInThreeNoUnitVariable (OneInThreeVariable Variable) :=
  variableMap sourceClauseIndex figureNineClauseStart source
    (zeroInheritedMap sourceClauseIndex source)

/-- Certified composed drawing instantiated at an arbitrary empty positioned
source clause. -/
def instantiatedZeroDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  letI := nestedVariableDecidableEq (Variable := Variable)
  (EmbeddedCNFIncidenceDrawing.renameToImage
    zeroDrawing
    (zeroVariableMap
      sourceClauseIndex figureNineClauseStart source)).translate
        (Cell.scale composedGadgetScale source.position)

/-- The instantiated empty drawing's formula is exactly its actual two-stage
positioned clause block. -/
theorem instantiatedZeroDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (sourceLiterals : source.literals = []) :
    (instantiatedZeroDrawing
      sourceClauseIndex figureNineClauseStart source).formula =
        composedClauseGadget
          sourceClauseIndex figureNineClauseStart source := by
  rcases source with ⟨sourcePosition, literals⟩
  dsimp at sourceLiterals ⊢
  subst literals
  simp [instantiatedZeroDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    zeroDrawing, zeroFormula,
    forcedFalseUnitReplacement, clause,
    zeroVariableMap, variableMap, zeroInheritedMap,
    figureNineClauseLiterals,
    composedClauseGadget,
    PeriodicOneInThreePositioned.clauseGadget,
    PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
    PlanarOneInThreeNoUnits.embedPositionedClause,
    PeriodicOneInThree.clauseClauses,
    PeriodicOneInThreeNoUnits.clauseClauses,
    PeriodicOneInThree.disjunctionGadget,
    PeriodicOneInThree.padding,
    PeriodicOneInThree.forcePaddingFalse,
    PeriodicOneInThree.auxiliary,
    PeriodicOneInThree.negate,
    PlanarOneInThree.generatedClausePosition,
    composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    EmbeddedClause.rename, EmbeddedClause.map,
    EmbeddedClause.translate, Cell.add, Cell.scale]
  unfold
    PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition
  simp [PeriodicOneInThreeNoUnits.liftLiteral,
    PeriodicOneInThreeNoUnits.auxiliary,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.scale]
  omega

/-- The empty-source map is injective on every occurring finite role. -/
theorem zeroVariableMap_injectiveOn
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    ∀ left ∈ zeroDrawing.variableVertices,
      ∀ right ∈ zeroDrawing.variableVertices,
        zeroVariableMap
            sourceClauseIndex figureNineClauseStart source left =
          zeroVariableMap
            sourceClauseIndex figureNineClauseStart source right →
        left = right := by
  intro left leftMember right rightMember equal
  simp [EmbeddedCNFIncidenceDrawing.variableVertices,
    zeroDrawing, zeroFormula, forcedFalseUnitReplacement,
    clause] at leftMember rightMember
  cases left with
  | inherited leftRole =>
      cases right with
      | inherited rightRole =>
          cases leftRole <;> cases rightRole <;>
            simp_all [zeroVariableMap, variableMap,
              zeroInheritedMap]
      | unitAux rightIndex rightKind =>
          simp [zeroVariableMap, variableMap] at equal
  | unitAux leftIndex leftKind =>
      cases right with
      | inherited rightRole =>
          simp [zeroVariableMap, variableMap] at equal
      | unitAux rightIndex rightKind =>
          cases leftKind <;> cases rightKind <;>
            simp_all [zeroVariableMap, variableMap]

/-- Every genuine empty instance inherits the complete finite geometric
certificate. -/
theorem instantiatedZeroDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    @EmbeddedCNFIncidenceDrawing.IsValid
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
      nestedVariableDecidableEq
      (instantiatedZeroDrawing
        sourceClauseIndex figureNineClauseStart source) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  apply EmbeddedCNFIncidenceDrawing.isValid_translate
  apply EmbeddedCNFIncidenceDrawing.renameToImage_isValid
  · exact zeroVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart source
  · exact zeroDrawing_isValid

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

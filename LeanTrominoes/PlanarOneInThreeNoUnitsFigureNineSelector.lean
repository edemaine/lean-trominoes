import LeanTrominoes.PlanarOneInThreeLocalDistinctness
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineInstantiation

/-!
# Uniform selection of composed Figure 9 drawings

The four certified Figure 9-plus-unit-elimination instances are packaged
behind one total selector.  For a width-three source clause the selected
drawing embeds exactly the actual two-stage positioned clause block, and
source-atom distinctness supplies its complete geometric certificate.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

local instance nestedDecidableEqInstance
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  nestedVariableDecidableEq

/-- Select the composed drawing determined by a positioned source clause's
arity.  Inputs beyond width three use the ternary prefix as a total
fallback. -/
def instantiatedDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  match source.literals with
  | [] =>
      instantiatedZeroDrawing
        sourceClauseIndex figureNineClauseStart source
  | [first] =>
      instantiatedOneDrawing
        sourceClauseIndex figureNineClauseStart source first
  | [first, second] =>
      instantiatedTwoDrawing
        sourceClauseIndex figureNineClauseStart source first second
  | first :: second :: third :: _ =>
      instantiatedThreeDrawing
        sourceClauseIndex figureNineClauseStart source
        first second third

/-- The finite certified template selected by a source clause's arity. -/
def templateDrawing
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable) :
    EmbeddedCNFIncidenceDrawing FigureNineNoUnitsVariable :=
  match source.literals with
  | [] => zeroDrawing
  | [first] => oneDrawingFor first.value
  | [first, second] =>
      twoDrawingFor first.value second.value
  | first :: second :: third :: _ =>
      fullDrawingFor first.value second.value third.value

/-- The actual nested-variable map selected by a source clause's arity. -/
def instantiatedVariableMap
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    FigureNineNoUnitsVariable →
      OneInThreeNoUnitVariable (OneInThreeVariable Variable) :=
  match source.literals with
  | [] =>
      zeroVariableMap
        sourceClauseIndex figureNineClauseStart source
  | [first] =>
      oneVariableMap
        sourceClauseIndex figureNineClauseStart source
        first.atom
  | [first, second] =>
      twoVariableMap
        sourceClauseIndex figureNineClauseStart source
        first.atom second.atom
  | first :: second :: third :: _ =>
      threeVariableMap
        sourceClauseIndex figureNineClauseStart source
        first.atom second.atom third.atom

/-- The uniform selector is the selected finite template renamed by the
selected actual-variable map and translated into the source macrocell. -/
theorem instantiatedDrawing_eq
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    instantiatedDrawing
        sourceClauseIndex figureNineClauseStart source =
      (EmbeddedCNFIncidenceDrawing.renameToImage
        (templateDrawing source)
        (instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source)).translate
        (Cell.scale composedGadgetScale source.position) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, tail⟩ <;> rfl

/-- Width three and source-atom distinctness make the selected actual
variable map injective on every role occurring in the selected template. -/
theorem instantiatedVariableMap_injectiveOn
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup) :
    ∀ left ∈ (templateDrawing source).variableVertices,
      ∀ right ∈ (templateDrawing source).variableVertices,
        instantiatedVariableMap
            sourceClauseIndex figureNineClauseStart source left =
          instantiatedVariableMap
            sourceClauseIndex figureNineClauseStart source right →
        left = right := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact zeroVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart
      ⟨sourcePosition, []⟩
  · rcases rest with _ | ⟨second, rest⟩
    · exact oneVariableMap_injectiveOn
        sourceClauseIndex figureNineClauseStart
        ⟨sourcePosition, [first]⟩ first
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond :
            first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact twoVariableMap_injectiveOn
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second]⟩
          first second firstNeSecond
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact threeVariableMap_injectiveOn
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second, third]⟩
          first second third
          pairwise.1.1 pairwise.1.2 pairwise.2

/-- The variables occurring in a selected instantiated drawing are exactly
the image of the variables occurring in its selected finite template. -/
theorem instantiatedDrawing_variableVertices
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).variableVertices =
      (templateDrawing source).variableVertices.map
        (instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rw [instantiatedDrawing_eq,
    EmbeddedCNFIncidenceDrawing.variableVertices_translate]
  unfold EmbeddedCNFIncidenceDrawing.renameToImage
  apply EmbeddedCNFIncidenceDrawing.variableVertices_rename
  exact instantiatedVariableMap_injectiveOn
    sourceClauseIndex figureNineClauseStart
    source width distinct

/-- Every occurring finite role retains its exact translated template
position under the uniform arity selector. -/
theorem instantiatedDrawing_rolePosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup)
    (role : FigureNineNoUnitsVariable)
    (roleMember :
      role ∈ (templateDrawing source).variableVertices) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).variablePosition
        (instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source role) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        ((templateDrawing source).variablePosition role) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rw [instantiatedDrawing_eq]
  change
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        (templateDrawing source)
        (instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source)
        (instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source role)) =
    Cell.add
      (Cell.scale composedGadgetScale source.position)
      ((templateDrawing source).variablePosition role)
  rw [EmbeddedCNFIncidenceDrawing.imageVariablePosition_map
    (templateDrawing source)
    (instantiatedVariableMap
      sourceClauseIndex figureNineClauseStart source)
    (instantiatedVariableMap_injectiveOn
      sourceClauseIndex figureNineClauseStart
      source width distinct)
    role roleMember]

/-- For a width-three source, the selected drawing's formula is exactly the
actual composed positioned clause block. -/
theorem instantiatedDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).formula =
        composedClauseGadget
          sourceClauseIndex figureNineClauseStart source := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedZeroDrawing_formula
      sourceClauseIndex figureNineClauseStart
      ⟨sourcePosition, []⟩ rfl
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedOneDrawing_formula
        sourceClauseIndex figureNineClauseStart
        ⟨sourcePosition, [first]⟩ first rfl
    · rcases rest with _ | ⟨third, tail⟩
      · exact instantiatedTwoDrawing_formula
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second]⟩
          first second rfl
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        exact instantiatedThreeDrawing_formula
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second, third]⟩
          first second third rfl

/-- Width at most three and pairwise distinct source atoms make the selected
composed drawing valid. -/
theorem instantiatedDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup) :
    @EmbeddedCNFIncidenceDrawing.IsValid
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
      nestedVariableDecidableEq
      (instantiatedDrawing
        sourceClauseIndex figureNineClauseStart source) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact instantiatedZeroDrawing_isValid
      sourceClauseIndex figureNineClauseStart
      ⟨sourcePosition, []⟩
  · rcases rest with _ | ⟨second, rest⟩
    · exact instantiatedOneDrawing_isValid
        sourceClauseIndex figureNineClauseStart
        ⟨sourcePosition, [first]⟩ first
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedTwoDrawing_isValid
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second]⟩
          first second firstNeSecond
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        exact instantiatedThreeDrawing_isValid
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [first, second, third]⟩
          first second third
          pairwise.1.1 pairwise.1.2 pairwise.2

/-- Boundary port assigned to an original source literal by its index in the
complete composed Figure 9-plus-unit-elimination neighborhood. -/
def sourceLocalPosition : Nat → Cell
  | 0 => (36, 0)
  | 1 => (0, 30)
  | _ => (72, 30)

/-- Every genuine original source literal is placed at the composed
neighborhood boundary port selected by its source-clause index. -/
theorem instantiatedDrawing_sourcePosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ source.literals.zipIdx) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).variablePosition
        (.inl (.inl literal.atom)) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        (sourceLocalPosition literalIndex) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp at literalMember
  · rcases rest with _ | ⟨second, rest⟩
    · simp at literalMember
      rcases literalMember with ⟨rfl, rfl⟩
      have roleMember :
          .inherited PlanarOneInThree.FigureNineVariable.sourceFirst ∈
            (oneDrawingFor literal.value).variableVertices := by
        simp [oneDrawingFor, oneFormulaFor,
          forcedFalseUnitReplacement, clause,
          EmbeddedCNFIncidenceDrawing.variableVertices]
      have rolePosition :=
        instantiatedOneDrawing_rolePosition
          sourceClauseIndex figureNineClauseStart
          ⟨sourcePosition, [literal]⟩ literal
          (.inherited
            PlanarOneInThree.FigureNineVariable.sourceFirst)
          roleMember
      simpa [instantiatedDrawing,
        oneDrawingFor,
        oneVariableMap, variableMap, oneInheritedMap,
        variablePosition,
        PlanarOneInThree.figureNineVariablePosition,
        sourceLocalPosition, Cell.scale, Cell.add] using rolePosition
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond :
            first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        simp at literalMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have roleMember :
              .inherited
                  PlanarOneInThree.FigureNineVariable.sourceFirst ∈
                (twoDrawingFor
                  literal.value second.value).variableVertices := by
            simp [twoDrawingFor, twoFormulaFor,
              forcedFalseUnitReplacement, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          have rolePosition :=
            instantiatedTwoDrawing_rolePosition
              sourceClauseIndex figureNineClauseStart
              ⟨sourcePosition, [literal, second]⟩
              literal second firstNeSecond
              (.inherited
                PlanarOneInThree.FigureNineVariable.sourceFirst)
              roleMember
          simpa [instantiatedDrawing,
            twoDrawingFor,
            twoVariableMap, variableMap, twoInheritedMap,
            variablePosition,
            PlanarOneInThree.figureNineVariablePosition,
            sourceLocalPosition, Cell.scale, Cell.add] using rolePosition
        · have roleMember :
              .inherited
                  PlanarOneInThree.FigureNineVariable.sourceSecond ∈
                (twoDrawingFor
                  first.value literal.value).variableVertices := by
            simp [twoDrawingFor, twoFormulaFor,
              forcedFalseUnitReplacement, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          have rolePosition :=
            instantiatedTwoDrawing_rolePosition
              sourceClauseIndex figureNineClauseStart
              ⟨sourcePosition, [first, literal]⟩
              first literal firstNeSecond
              (.inherited
                PlanarOneInThree.FigureNineVariable.sourceSecond)
              roleMember
          simpa [instantiatedDrawing,
            twoDrawingFor,
            twoVariableMap, variableMap, twoInheritedMap,
            variablePosition,
            PlanarOneInThree.figureNineVariablePosition,
            sourceLocalPosition, Cell.scale, Cell.add] using rolePosition
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup]
            using distinct
        simp at literalMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have roleMember :
              .inherited
                  PlanarOneInThree.FigureNineVariable.sourceFirst ∈
                (fullDrawingFor literal.value second.value
                  third.value).variableVertices := by
            simp [fullDrawingFor, fullFormulaFor, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          have rolePosition :=
            instantiatedThreeDrawing_rolePosition
              sourceClauseIndex figureNineClauseStart
              ⟨sourcePosition, [literal, second, third]⟩
              literal second third
              pairwise.1.1 pairwise.1.2 pairwise.2
              (.inherited
                PlanarOneInThree.FigureNineVariable.sourceFirst)
              roleMember
          simpa [instantiatedDrawing,
            fullDrawingFor,
            threeVariableMap, variableMap, threeInheritedMap,
            variablePosition,
            PlanarOneInThree.figureNineVariablePosition,
            sourceLocalPosition, Cell.scale, Cell.add] using rolePosition
        · have roleMember :
              .inherited
                  PlanarOneInThree.FigureNineVariable.sourceSecond ∈
                (fullDrawingFor first.value literal.value
                  third.value).variableVertices := by
            simp [fullDrawingFor, fullFormulaFor, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          have rolePosition :=
            instantiatedThreeDrawing_rolePosition
              sourceClauseIndex figureNineClauseStart
              ⟨sourcePosition, [first, literal, third]⟩
              first literal third
              pairwise.1.1 pairwise.1.2 pairwise.2
              (.inherited
                PlanarOneInThree.FigureNineVariable.sourceSecond)
              roleMember
          simpa [instantiatedDrawing,
            fullDrawingFor,
            threeVariableMap, variableMap, threeInheritedMap,
            variablePosition,
            PlanarOneInThree.figureNineVariablePosition,
            sourceLocalPosition, Cell.scale, Cell.add] using rolePosition
        · have roleMember :
              .inherited
                  PlanarOneInThree.FigureNineVariable.sourceThird ∈
                (fullDrawingFor first.value second.value
                  literal.value).variableVertices := by
            simp [fullDrawingFor, fullFormulaFor, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          have rolePosition :=
            instantiatedThreeDrawing_rolePosition
              sourceClauseIndex figureNineClauseStart
              ⟨sourcePosition, [first, second, literal]⟩
              first second literal
              pairwise.1.1 pairwise.1.2 pairwise.2
              (.inherited
                PlanarOneInThree.FigureNineVariable.sourceThird)
              roleMember
          simpa [instantiatedDrawing,
            fullDrawingFor,
            threeVariableMap, variableMap, threeInheritedMap,
            variablePosition,
            PlanarOneInThree.figureNineVariablePosition,
            sourceLocalPosition, Cell.scale, Cell.add] using rolePosition

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

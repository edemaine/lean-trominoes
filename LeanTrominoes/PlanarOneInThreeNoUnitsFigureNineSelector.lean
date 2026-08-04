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

private theorem routeAt_incidenceAt_eq_of_drawing_eq
    {Variable : Type*}
    {first second : EmbeddedCNFIncidenceDrawing Variable}
    (equal : first = second)
    (index : Fin first.incidences.length) :
    first.routeAt (first.incidenceAt index) =
      second.routeAt
        (second.incidenceAt
          (Fin.cast
            (congrArg
              (fun drawing : EmbeddedCNFIncidenceDrawing Variable =>
                drawing.incidences.length)
              equal)
            index)) := by
  subst second
  rfl

/-- Every presentation-indexed route in the selected instantiated drawing
is the corresponding finite-template route translated into the source
macrocell.  Logical renaming changes only incidence labels. -/
theorem instantiatedDrawing_routeAt_incidenceAt_eq
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (index : Fin
      (instantiatedDrawing
        sourceClauseIndex figureNineClauseStart source).incidences.length) :
    ∃ templateIndex : Fin (templateDrawing source).incidences.length,
      templateIndex.val = index.val ∧
        (instantiatedDrawing
            sourceClauseIndex figureNineClauseStart source).routeAt
              ((instantiatedDrawing
                sourceClauseIndex figureNineClauseStart source).incidenceAt
                  index) =
          PeriodicOrthocrossing.translatePolyline
            (Cell.scale composedGadgetScale source.position)
            ((templateDrawing source).routeAt
              ((templateDrawing source).incidenceAt templateIndex)) := by
  let template := templateDrawing source
  let variableMap :=
    instantiatedVariableMap
      sourceClauseIndex figureNineClauseStart source
  let renamed :=
    EmbeddedCNFIncidenceDrawing.renameToImage template variableMap
  let offset := Cell.scale composedGadgetScale source.position
  let target := renamed.translate offset
  have drawingEqual :
      instantiatedDrawing
          sourceClauseIndex figureNineClauseStart source = target := by
    simpa [target, renamed, template, variableMap, offset] using
      instantiatedDrawing_eq
        sourceClauseIndex figureNineClauseStart source
  let targetIndex : Fin target.incidences.length :=
    Fin.cast
      (congrArg
        (fun drawing :
          EmbeddedCNFIncidenceDrawing
            (OneInThreeNoUnitVariable
              (OneInThreeVariable Variable)) =>
          drawing.incidences.length)
        drawingEqual)
      index
  let renamedIndex : Fin renamed.incidences.length :=
    ⟨targetIndex.val, targetIndex.isLt.trans_eq
      (EmbeddedCNFIncidenceDrawing.translate_incidences_length
        renamed offset)⟩
  let templateIndex : Fin template.incidences.length :=
    ⟨renamedIndex.val, renamedIndex.isLt.trans_eq
      (EmbeddedCNFIncidenceDrawing.rename_incidences_length
        template variableMap
        (EmbeddedCNFIncidenceDrawing.imageVariablePosition
          template variableMap))⟩
  refine ⟨templateIndex, ?_, ?_⟩
  · simp [templateIndex, renamedIndex, targetIndex]
  have selectedRouteEqual :
      (instantiatedDrawing
          sourceClauseIndex figureNineClauseStart source).routeAt
            ((instantiatedDrawing
              sourceClauseIndex figureNineClauseStart source).incidenceAt
                index) =
        target.routeAt (target.incidenceAt targetIndex) := by
    simpa [targetIndex] using
      routeAt_incidenceAt_eq_of_drawing_eq drawingEqual index
  have translatedIncidence :=
    EmbeddedCNFIncidenceDrawing.incidenceAt_translate
      renamed offset targetIndex
  have renamedIncidence :=
    EmbeddedCNFIncidenceDrawing.incidenceAt_rename
      template variableMap
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        template variableMap)
      renamedIndex
  rw [selectedRouteEqual]
  change
    (renamed.translate offset).routeAt
        ((renamed.translate offset).incidenceAt targetIndex) = _
  rw [translatedIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt_translate_incidence]
  have renamedIndexEqual :
      (⟨targetIndex.val, by
        exact targetIndex.isLt.trans_eq
          (EmbeddedCNFIncidenceDrawing.translate_incidences_length
            renamed offset)⟩ : Fin renamed.incidences.length) =
        renamedIndex := by
    apply Fin.ext
    rfl
  rw [renamedIndexEqual]
  change
    List.map (Cell.add offset)
        ((template.rename variableMap
          (EmbeddedCNFIncidenceDrawing.imageVariablePosition
            template variableMap)).routeAt
          ((template.rename variableMap
            (EmbeddedCNFIncidenceDrawing.imageVariablePosition
              template variableMap)).incidenceAt renamedIndex)) = _
  rw [renamedIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt_rename_incidence]
  rfl

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

/-- Every variable occurring in an instantiated drawing comes from one
occurring finite role, and therefore retains that role's translated template
position. -/
theorem instantiatedDrawing_exists_role
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup)
    {atom :
      OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)}
    (atomMember :
      atom ∈
        (instantiatedDrawing
          sourceClauseIndex figureNineClauseStart source).variableVertices) :
    ∃ role,
      role ∈ (templateDrawing source).variableVertices ∧
      instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source role = atom ∧
      (instantiatedDrawing
        sourceClauseIndex figureNineClauseStart source).variablePosition
          atom =
        Cell.add
          (Cell.scale composedGadgetScale source.position)
          ((templateDrawing source).variablePosition role) := by
  rw [instantiatedDrawing_variableVertices
    sourceClauseIndex figureNineClauseStart
    source width distinct] at atomMember
  rcases List.mem_map.mp atomMember with
    ⟨role, roleMember, roleEqual⟩
  refine ⟨role, roleMember, roleEqual, ?_⟩
  rw [← roleEqual]
  exact instantiatedDrawing_rolePosition
    sourceClauseIndex figureNineClauseStart
    source width distinct role roleMember

/-- All arity-specific finite templates use the same composed variable
positions. -/
@[simp]
theorem templateDrawing_variablePosition
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable)
    (role : FigureNineNoUnitsVariable) :
    (templateDrawing source).variablePosition role =
      variablePosition role := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, tail⟩ <;> rfl

/-- The uniform actual-variable selector maps a finite second-stage
auxiliary role to its globally scoped nested auxiliary. -/
@[simp]
theorem instantiatedVariableMap_unitAux
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (localClauseIndex : Nat)
    (kind : OneInThreeNoUnitAux) :
    instantiatedVariableMap
        sourceClauseIndex figureNineClauseStart source
        (.unitAux localClauseIndex kind) =
      .inr
        ((figureNineClauseStart + localClauseIndex,
          figureNineClauseLiterals
            sourceClauseIndex source localClauseIndex),
          kind) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, tail⟩ <;> rfl

/-- Every occurring second-stage auxiliary has the physical position
declared by its local Figure 9 clause index. -/
theorem instantiatedDrawing_unitAuxiliaryPosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup)
    (localClauseIndex : Nat)
    (kind : OneInThreeNoUnitAux)
    (atomMember :
      (.inr
        ((figureNineClauseStart + localClauseIndex,
          figureNineClauseLiterals
            sourceClauseIndex source localClauseIndex),
          kind) :
        OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)) ∈
        (instantiatedDrawing
          sourceClauseIndex figureNineClauseStart source).variableVertices) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).variablePosition
        (.inr
          ((figureNineClauseStart + localClauseIndex,
            figureNineClauseLiterals
              sourceClauseIndex source localClauseIndex),
            kind)) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        (Cell.add
          (Cell.scale
            6
            (PlanarOneInThree.generatedClausePosition
              (0, 0) localClauseIndex))
          (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition
            kind)) := by
  rcases instantiatedDrawing_exists_role
      sourceClauseIndex figureNineClauseStart
      source width distinct atomMember with
    ⟨role, roleMember, roleEqual, rolePosition⟩
  cases role with
  | inherited role =>
      rcases source with ⟨sourcePosition, literals⟩
      rcases literals with _ | ⟨first, rest⟩
      · simp [instantiatedVariableMap, zeroVariableMap,
          variableMap] at roleEqual
      · rcases rest with _ | ⟨second, rest⟩
        · simp [instantiatedVariableMap, oneVariableMap,
            variableMap] at roleEqual
        · rcases rest with _ | ⟨third, tail⟩ <;>
            simp [instantiatedVariableMap,
              twoVariableMap, threeVariableMap,
              variableMap] at roleEqual
  | unitAux roleIndex roleKind =>
      have roleData :
          (figureNineClauseStart + roleIndex =
              figureNineClauseStart + localClauseIndex ∧
            figureNineClauseLiterals
                sourceClauseIndex source roleIndex =
              figureNineClauseLiterals
                sourceClauseIndex source localClauseIndex) ∧
            roleKind = kind := by
        simpa only [instantiatedVariableMap_unitAux,
          Sum.inr.injEq, Prod.mk.injEq] using roleEqual
      have scopeEqual :
          figureNineClauseStart + roleIndex =
            figureNineClauseStart + localClauseIndex := by
        exact roleData.1.1
      have roleIndexEqual : roleIndex = localClauseIndex := by
        omega
      have roleKindEqual : roleKind = kind := by
        exact roleData.2
      subst roleIndex
      subst roleKind
      simpa [variablePosition] using rolePosition

/-- Every occurring first-stage Figure 9 auxiliary retains its sixfold
scaled Figure 9 variable position inside the composed source macrocell. -/
theorem instantiatedDrawing_figureNineAuxiliaryPosition
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup)
    (kind : OneInThreeAux)
    (atomMember :
      (.inl
        (.inr
          ((sourceClauseIndex, source.literals), kind)) :
        OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)) ∈
        (instantiatedDrawing
          sourceClauseIndex figureNineClauseStart source).variableVertices) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).variablePosition
        (.inl
          (.inr
            ((sourceClauseIndex, source.literals), kind))) =
      Cell.add
        (Cell.scale composedGadgetScale source.position)
        (Cell.scale 6
          (PeriodicOneInThreePositioned.auxiliaryLocalPosition kind)) := by
  rcases instantiatedDrawing_exists_role
      sourceClauseIndex figureNineClauseStart
      source width distinct atomMember with
    ⟨role, roleMember, roleEqual, rolePosition⟩
  cases role with
  | unitAux roleIndex roleKind =>
      simp at roleEqual
  | inherited role =>
      have finitePosition :
          PlanarOneInThree.figureNineVariablePosition role =
            PeriodicOneInThreePositioned.auxiliaryLocalPosition kind := by
        rcases source with ⟨sourcePosition, literals⟩
        rcases literals with _ | ⟨first, rest⟩
        · simp [templateDrawing, zeroDrawing, zeroFormula,
              forcedFalseUnitReplacement, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
              at roleMember
          cases role <;>
            simp_all [instantiatedVariableMap,
              zeroVariableMap, variableMap, zeroInheritedMap,
              PlanarOneInThree.figureNineVariablePosition]
        · rcases rest with _ | ⟨second, rest⟩
          · simp [templateDrawing, oneDrawingFor, oneFormulaFor,
                forcedFalseUnitReplacement, clause,
                EmbeddedCNFIncidenceDrawing.variableVertices]
                at roleMember
            cases role <;>
              simp_all [instantiatedVariableMap,
                oneVariableMap, variableMap, oneInheritedMap,
                PlanarOneInThree.figureNineVariablePosition]
          · rcases rest with _ | ⟨third, tail⟩
            · simp [templateDrawing, twoDrawingFor, twoFormulaFor,
                  forcedFalseUnitReplacement, clause,
                  EmbeddedCNFIncidenceDrawing.variableVertices]
                  at roleMember
              cases role <;>
                simp_all [instantiatedVariableMap,
                  twoVariableMap, variableMap, twoInheritedMap,
                  PlanarOneInThree.figureNineVariablePosition]
            · simp [templateDrawing, fullDrawingFor,
                  fullFormulaFor, clause,
                  EmbeddedCNFIncidenceDrawing.variableVertices]
                  at roleMember
              cases role <;>
                simp_all [instantiatedVariableMap,
                  threeVariableMap, variableMap, threeInheritedMap,
                  PlanarOneInThree.figureNineVariablePosition]
      simpa [variablePosition, finitePosition] using rolePosition

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

/-- Every genuine original source literal is represented by a variable
vertex of the selected composed finite drawing. -/
theorem instantiatedDrawing_sourceAtom_mem_variableVertices
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (distinct : source.AtomsNodup)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ source.literals.zipIdx) :
    (.inl (.inl literal.atom) :
        OneInThreeNoUnitVariable (OneInThreeVariable Variable)) ∈
      (instantiatedDrawing
        sourceClauseIndex figureNineClauseStart source).variableVertices := by
  rw [instantiatedDrawing_variableVertices
    sourceClauseIndex figureNineClauseStart source width distinct]
  apply List.mem_map.mpr
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · simp at literalMember
  · rcases rest with _ | ⟨second, rest⟩
    · simp at literalMember
      rcases literalMember with ⟨rfl, rfl⟩
      refine
        ⟨.inherited PlanarOneInThree.FigureNineVariable.sourceFirst,
          ?_, ?_⟩
      · simp [templateDrawing, oneDrawingFor, oneFormulaFor,
          forcedFalseUnitReplacement, clause,
          EmbeddedCNFIncidenceDrawing.variableVertices]
      · simp [instantiatedVariableMap, oneVariableMap,
          variableMap, oneInheritedMap]
    · rcases rest with _ | ⟨third, tail⟩
      · have firstNeSecond : first.atom ≠ second.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup] using distinct
        simp at literalMember
        rcases literalMember with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine
            ⟨.inherited PlanarOneInThree.FigureNineVariable.sourceFirst,
              ?_, ?_⟩
          · simp [templateDrawing, twoDrawingFor, twoFormulaFor,
              forcedFalseUnitReplacement, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          · simp [instantiatedVariableMap, twoVariableMap,
              variableMap, twoInheritedMap]
        · refine
            ⟨.inherited PlanarOneInThree.FigureNineVariable.sourceSecond,
              ?_, ?_⟩
          · simp [templateDrawing, twoDrawingFor, twoFormulaFor,
              forcedFalseUnitReplacement, clause,
              EmbeddedCNFIncidenceDrawing.variableVertices]
          · simp [instantiatedVariableMap, twoVariableMap,
              variableMap, twoInheritedMap]
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        have pairwise :
            (first.atom ≠ second.atom ∧
              first.atom ≠ third.atom) ∧
            second.atom ≠ third.atom := by
          simpa [PositionedPeriodicClause.AtomsNodup] using distinct
        simp at literalMember
        rcases literalMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine
            ⟨.inherited PlanarOneInThree.FigureNineVariable.sourceFirst,
              ?_, ?_⟩
          · simp [templateDrawing, fullDrawingFor, fullFormulaFor,
              clause, EmbeddedCNFIncidenceDrawing.variableVertices]
          · simp [instantiatedVariableMap, threeVariableMap,
              variableMap, threeInheritedMap]
        · refine
            ⟨.inherited PlanarOneInThree.FigureNineVariable.sourceSecond,
              ?_, ?_⟩
          · simp [templateDrawing, fullDrawingFor, fullFormulaFor,
              clause, EmbeddedCNFIncidenceDrawing.variableVertices]
          · simp [instantiatedVariableMap, threeVariableMap,
              variableMap, threeInheritedMap]
        · refine
            ⟨.inherited PlanarOneInThree.FigureNineVariable.sourceThird,
              ?_, ?_⟩
          · simp [templateDrawing, fullDrawingFor, fullFormulaFor,
              clause, EmbeddedCNFIncidenceDrawing.variableVertices]
          · simp [instantiatedVariableMap, threeVariableMap,
              variableMap, threeInheritedMap]

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes

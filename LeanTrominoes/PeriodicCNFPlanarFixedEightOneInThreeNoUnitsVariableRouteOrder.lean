import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeNoUnitsRoutes
import LeanTrominoes.PositionedPeriodicCNFVariableRouteOrderRenaming

/-!
# Fixed-eight route order through unit elimination

This file carries the fixed-eight clockwise variable-route order through the
opaque Figure 9 wrapper and the final unit-elimination splice.  Only genuine
degree-three source variables require three-point source routes; fresh Figure
9 auxiliaries have no third occurrence and are excluded by the scoped generic
transport theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Figure 9 route-order transport composes with an opaque variable wrapper
when the wrapped occurrence lookup uses inexpensive classical equality.
Proving this once over an abstract source type prevents later specializations
from normalizing deeply nested derived equality instances. -/
private theorem
    PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder_renameWrapped_classical
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (sourceOrder :
      source.VariableRoutesInOccurrenceOrder sourceRoutes)
    (preserved :
      PeriodicOneInThreePositioned.PreservesOriginalRouteTerminalDirections
        source sourceRoutes outputRoutes) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (WrappedPeriodicVariable (OneInThreeVariable Variable))
      (Classical.decEq _)
      ((PeriodicOneInThreePositioned.formula source).rename
        WrappedPeriodicVariable.mk)
      outputRoutes := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_rename
      (OneInThreeVariable Variable)
      (WrappedPeriodicVariable (OneInThreeVariable Variable))
      (Classical.decEq _) (Classical.decEq _)
      (PeriodicOneInThreePositioned.formula source)
      outputRoutes
      WrappedPeriodicVariable.mk WrappedPeriodicVariable.original
  · intro atom
    rfl
  · intro atom
    cases atom
    rfl
  · apply
      @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
        (OneInThreeVariable Variable)
        (inferInstance) (Classical.decEq _)
        (PeriodicOneInThreePositioned.formula source)
        outputRoutes
    exact
      PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder
        source sourceWidth sourceRoutes outputRoutes sourceOrder preserved

/-- A wrapped Figure 9 variable with a third occurrence is the wrapper of
an embedded source variable, not a fresh Figure 9 auxiliary. -/
private theorem
    PeriodicOneInThreePositioned.exists_original_of_wrapped_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (rawEq : DecidableEq (OneInThreeVariable Variable))
    (wrappedEq :
      DecidableEq
        (WrappedPeriodicVariable (OneInThreeVariable Variable)))
    (source : PositionedPeriodicCNF Variable)
    (wrappedAtom :
      WrappedPeriodicVariable (OneInThreeVariable Variable))
    (third :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (WrappedPeriodicVariable (OneInThreeVariable Variable)))
    (thirdLookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (WrappedPeriodicVariable (OneInThreeVariable Variable))
          wrappedEq
          ((PeriodicOneInThreePositioned.formula source).rename
            WrappedPeriodicVariable.mk).erase
          wrappedAtom .third = some third) :
    ∃ atom : Variable, wrappedAtom.original = .inl atom := by
  have wrapperInjective :
      Function.Injective
        (@WrappedPeriodicVariable.mk
          (OneInThreeVariable Variable)) :=
    fun _first _second equal =>
      congrArg WrappedPeriodicVariable.original equal
  rw [show wrappedAtom =
        WrappedPeriodicVariable.mk wrappedAtom.original by
      cases wrappedAtom
      rfl,
    (@PositionedPeriodicCNF.occurrenceAt_rename
      (OneInThreeVariable Variable)
      (WrappedPeriodicVariable (OneInThreeVariable Variable))
      rawEq wrappedEq
      (PeriodicOneInThreePositioned.formula source)
      WrappedPeriodicVariable.mk wrapperInjective)]
    at thirdLookup
  rcases Option.map_eq_some_iff.mp thirdLookup with
    ⟨rawThird, rawThirdLookup, _thirdEqual⟩
  apply
    PeriodicOneInThree.exists_original_of_occurrenceAt_third
      source.erase wrappedAtom.original rawThird
  rw [←
    PeriodicEightOccurrenceSplitPositioned.occurrenceAt_eq_of_decidableEq
      rawEq _
      (PeriodicOneInThree.formula source.erase)
      wrappedAtom.original .third]
  simpa only [PeriodicOneInThreePositioned.erase_formula] using
    rawThirdLookup

/-- Unit-elimination route-order transport with a cheap output equality
instance.  Keeping the generic source type abstract avoids normalizing the
deep fixed-eight variable type when this theorem is specialized. -/
private theorem
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (sourceOrder :
      source.VariableRoutesInOccurrenceOrder sourceRoutes)
    (preserved :
      PeriodicOneInThreeNoUnitsPositioned.PreservesDegreeThreeOriginalRouteTerminalDirections
        source sourceRoutes outputRoutes) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (OneInThreeNoUnitVariable Variable)
      (Classical.decEq _)
      (PeriodicOneInThreeNoUnitsPositioned.formula source)
      outputRoutes := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable Variable)
      (inferInstance) (Classical.decEq _)
      (PeriodicOneInThreeNoUnitsPositioned.formula source)
      outputRoutes
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_of_preservesDegreeThree
      source sourceRoutes outputRoutes sourceOrder preserved

/-- Opaque wrapping preserves the clockwise route order of the raw
fixed-eight Figure 9 output. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      (Classical.decEq _) (inferInstance)
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)
  exact
    PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder_renameWrapped_classical
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
        input sourceWidth)
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes input)
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_preservesOriginalRouteTerminalDirections
        input sourceLocal sourceWidth sourceOccurrences)

/-- Every raw Figure 9 route incident to an embedded fixed-eight source
variable has at least three listed points. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_length_ge_three_of_original
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3)
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom :
      PeriodicPlanarThreeSATThreeVariable Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    3 ≤
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).length := by
  let source :=
    drawingAngularEightOccurrenceSplitPositionedFormula input
  let sourcePlacement :=
    drawingAngularEightOccurrenceSplitPlacement input
  let inherited :=
    drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
      input sourceLocal sourceWidth sourceOccurrences
  rcases
      PeriodicOneInThreePositioned.inheritedIncidenceData?_of_members
        source sourcePlacement
        (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
          input sourceWidth)
        (drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
          input sourceLocal sourceWidth sourceOccurrences)
        clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  dsimp [source, sourcePlacement] at dataLookup
  have inheritedLength :
      2 ≤ (inherited.routes clauseIndex literalIndex).length := by
    simp [inherited,
      drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes,
      PeriodicOneInThreePositioned.inheritedRouteSuffixes,
      PeriodicOneInThreePositioned.inheritedRouteSuffixesRoutes,
      dataLookup,
      PeriodicOneInThreePositioned.inheritedRouteSuffix,
      joinAtEndpoint,
      PositionedPeriodicCNF.orthogonalDetour]
  simpa [drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
    source, sourcePlacement, inherited] using
    PeriodicOneInThreePositioned.splicedRoutes_length_ge_three_inherited
      source sourcePlacement
      (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
        input sourceWidth)
      (drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
        input sourceLocal sourceWidth sourceOccurrences)
      inherited clauseMember literalMember
      sourceAtom literalSource inheritedLength

/-- Every route of a wrapped variable that reaches the third occurrence
slot has at least three listed points.  Figure 9 occurrence provenance
reduces this scoped claim to the raw embedded-source route bound. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_length_ge_three_of_third
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3)
    (atom :
      WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
    (sourceThird :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (thirdLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
            input).erase
          atom .third = some sourceThird)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (literalAtom : literal.atom = atom) :
    3 ≤
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).length := by
  have genericThirdLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          ((PeriodicOneInThreePositioned.formula
            (drawingAngularEightOccurrenceSplitPositionedFormula
              input)).rename WrappedPeriodicVariable.mk).erase
          atom .third = some sourceThird := by
    simpa
      [drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula,
        drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula]
      using thirdLookup
  rcases
      @PeriodicOneInThreePositioned.exists_original_of_wrapped_occurrenceAt_third
        (PeriodicPlanarThreeSATThreeVariable Variable)
        (inferInstance) (inferInstance) (inferInstance)
        (drawingAngularEightOccurrenceSplitPositionedFormula input)
        atom sourceThird genericThirdLookup with
    ⟨sourceAtom, atomOriginal⟩
  rcases
      PositionedPeriodicCNF.exists_incidence_of_rename_members
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          input)
        WrappedPeriodicVariable.mk clauseMember literalMember with
    ⟨rawClause, rawLiteral, rawClauseMember, rawLiteralMember,
      literalRenamed⟩
  have atomRenamed :
      atom = WrappedPeriodicVariable.mk rawLiteral.atom := by
    rw [← literalAtom]
    exact literalRenamed
  have rawLiteralSource :
      rawLiteral.atom = .inl sourceAtom :=
    (congrArg WrappedPeriodicVariable.original atomRenamed).symm.trans
      atomOriginal
  simpa
    [drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes] using
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_length_ge_three_of_original
      input sourceLocal sourceWidth sourceOccurrences
      rawClauseMember rawLiteralMember sourceAtom rawLiteralSource

/-- The final unit-elimination splice preserves every terminal direction
needed by a genuine degree-three wrapped Figure 9 variable. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PeriodicOneInThreeNoUnitsPositioned.PreservesDegreeThreeOriginalRouteTerminalDirections
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences) := by
  simpa
    [drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
      drawingFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes]
    using
      PeriodicOneInThreeNoUnitsPositioned.preservesDegreeThreeOriginalRouteTerminalDirections_splicedRoutes
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
        (drawingFixedEightPeriodicPlanarOneInThreePlacement input)
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          input)
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
          input)
        (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          input sourceLocal sourceWidth sourceOccurrences)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
              input sourceLocal sourceWidth sourceOccurrences
              sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
            input sourceLocal sourceWidth sourceOccurrences
            sourceClauseMember sourceLiteralMember).2.2)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
            input sourceLocal sourceWidth sourceOccurrences
            sourceClauseMember sourceLiteralMember)
        (fun atom sourceThird thirdLookup
            _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember
            literalAtom =>
          drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_length_ge_three_of_third
            input sourceLocal sourceWidth sourceOccurrences
            atom sourceThird thirdLookup
            sourceClauseMember sourceLiteralMember literalAtom)

/-- The final fixed-eight unit-free route family meets variable incidences
in syntactic occurrence order clockwise. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
      (Classical.decEq _) (inferInstance)
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        input)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
      (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula input)
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
        input sourceLocal sourceWidth sourceOccurrences)

end PeriodicOrthocrossing
end LeanTrominoes

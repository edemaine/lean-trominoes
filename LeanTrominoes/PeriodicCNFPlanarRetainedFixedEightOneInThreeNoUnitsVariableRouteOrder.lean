import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreeNoUnitsRoutes
import LeanTrominoes.PeriodicOneInThreeWrappedVariableRouteOrderTransport

/-!
# Retained fixed-eight route order through unit elimination

This file specializes the fixed-eight clockwise route-order argument to the
retained planar-SAT hardness pipeline.  The retained source supplies the
same eight-port angular split, but additionally depends on the final
planar-SAT certificate and its nonempty-clause hypothesis.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- The retained fixed-eight source routes follow syntactic occurrence order
clockwise at every degree-three split variable. -/
theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source) := by
  apply
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
  exact
    retainedDrawingAngularOccurrenceOrder_fitsEightSlots
      sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty

/-- Every retained fixed-eight source route contains a genuine final edge. -/
theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source clauseIndex literalIndex).length := by
  simpa
    [retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes,
      retainedDrawingEightOccurrenceSplitPositionedFormula,
      PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes]
    using
      PeriodicEightOccurrenceSplitPositioned.angularSplicedIncidenceRoutes_length_ge_two
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
        (retainedDrawingAngularOccurrenceOrder source)
        (PeriodicEightOccurrenceSplitPositioned.canonicalAngularBoundaryRoutes
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            source)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
          (retainedDrawingAngularOccurrenceOrder source))
        clauseMember literalMember

/-- The raw retained Figure 9 splice preserves terminal direction on every
inherited fixed-eight incidence. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_preservesOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreePositioned.PreservesOriginalRouteTerminalDirections
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes]
    using
      PeriodicOneInThreePositioned.preservesOriginalRouteTerminalDirections_splicedRoutes
        (retainedDrawingEightOccurrenceSplitPositionedFormula source)
        (retainedDrawingEightOccurrenceSplitPlacement source)
        (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
          source)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_endpoints
            source sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_orthogonal
            source sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_length_ge_two
            source sourceClauseMember sourceLiteralMember)

/-- Opaque wrapping preserves the retained raw Figure 9 clockwise route
order. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      (Classical.decEq _) (inferInstance)
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder_renameWrapped_classical
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_preservesOriginalRouteTerminalDirections
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- Every raw retained Figure 9 route incident to an embedded fixed-eight
source variable has at least three listed points. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_length_ge_three_of_original
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).clauses.zipIdx)
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
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).length := by
  let splitSource :=
    retainedDrawingEightOccurrenceSplitPositionedFormula source
  let sourcePlacement :=
    retainedDrawingEightOccurrenceSplitPlacement source
  let inherited :=
    retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rcases
      PeriodicOneInThreePositioned.inheritedIncidenceData?_of_members
        splitSource sourcePlacement
        (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  dsimp [splitSource, sourcePlacement] at dataLookup
  have inheritedLength :
      2 ≤ (inherited.routes clauseIndex literalIndex).length := by
    simp [inherited,
      retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes,
      PeriodicOneInThreePositioned.inheritedRouteSuffixes,
      PeriodicOneInThreePositioned.inheritedRouteSuffixesRoutes,
      dataLookup,
      PeriodicOneInThreePositioned.inheritedRouteSuffix,
      joinAtEndpoint,
      PositionedPeriodicCNF.orthogonalDetour]
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      splitSource, sourcePlacement, inherited] using
    PeriodicOneInThreePositioned.splicedRoutes_length_ge_three_inherited
      splitSource sourcePlacement
      (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      inherited clauseMember literalMember
      sourceAtom literalSource inheritedLength

/-- Every retained wrapped route of a variable that reaches the third
occurrence slot has at least three listed points. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_length_ge_three_of_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (atom :
      WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
    (sourceThird :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (thirdLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
            source).erase
          atom .third = some sourceThird)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (literalAtom : literal.atom = atom) :
    3 ≤
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).length := by
  have genericThirdLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          ((PeriodicOneInThreePositioned.formula
            (retainedDrawingEightOccurrenceSplitPositionedFormula
              source)).rename WrappedPeriodicVariable.mk).erase
          atom .third = some sourceThird := by
    simpa
      [retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
        retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula]
      using thirdLookup
  rcases
      @PeriodicOneInThreePositioned.exists_original_of_wrapped_occurrenceAt_third
        (PeriodicPlanarThreeSATThreeVariable Variable)
        (inferInstance) (inferInstance) (inferInstance)
        (retainedDrawingEightOccurrenceSplitPositionedFormula source)
        atom sourceThird genericThirdLookup with
    ⟨sourceAtom, atomOriginal⟩
  rcases
      PositionedPeriodicCNF.exists_incidence_of_rename_members
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source)
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
    [retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes] using
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_length_ge_three_of_original
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty rawClauseMember rawLiteralMember
      sourceAtom rawLiteralSource

/-- The retained unit-elimination splice preserves every terminal direction
needed by a degree-three wrapped Figure 9 variable. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreeNoUnitsPositioned.PreservesDegreeThreeOriginalRouteTerminalDirections
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
      retainedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes]
    using
      PeriodicOneInThreeNoUnitsPositioned.preservesDegreeThreeOriginalRouteTerminalDirections_splicedRoutes
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
        (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
          source)
        (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty
              sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember).2.2)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember)
        (fun atom sourceThird thirdLookup
            _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember
            literalAtom =>
          retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_length_ge_three_of_third
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty atom sourceThird thirdLookup
            sourceClauseMember sourceLiteralMember literalAtom)

/-- The final retained unit-free route family meets variable incidences in
syntactic occurrence order clockwise. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
      (Classical.decEq _) (inferInstance)
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
      (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula source)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes

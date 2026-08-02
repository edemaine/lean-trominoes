import LeanTrominoes.RetainedAngularFanFinalNormalizedVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes
import LeanTrominoes.PeriodicOneInThreeWrappedVariableRouteOrderTransport

/-!
# Coordinated route order through exact-one transformations

This file transports the final coordinated fixed-eight clockwise route order
through the positioned Figure 9 construction, opaque wrapping, and unit
elimination.  The preceding route-length certificate supplies exactly the
nondegeneracy needed by both generic terminal-direction splice theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- The raw coordinated Figure 9 splice preserves terminal direction on
every inherited fixed-eight incidence. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_preservesOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreePositioned.PreservesOriginalRouteTerminalDirections
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa
    [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes]
    using
      PeriodicOneInThreePositioned.preservesOriginalRouteTerminalDirections_splicedRoutes
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember).2.2)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_length_ge_two
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember)

/-- Opaque wrapping preserves the coordinated raw Figure 9 clockwise route
order. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (WrappedPeriodicVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      (Classical.decEq _) (inferInstance)
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder_renameWrapped_classical
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_preservesOriginalRouteTerminalDirections
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- Every raw coordinated Figure 9 route incident to an embedded
fixed-eight source variable has at least three listed points. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_length_ge_three_of_original
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
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
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
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).length := by
  let splitSource :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source
  let sourcePlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let inherited :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rcases
      PeriodicOneInThreePositioned.inheritedIncidenceData?_of_members
        splitSource sourcePlacement
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  dsimp [splitSource, sourcePlacement] at dataLookup
  have inheritedLength :
      2 ≤ (inherited.routes clauseIndex literalIndex).length := by
    simp [inherited,
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes,
      PeriodicOneInThreePositioned.inheritedRouteSuffixes,
      PeriodicOneInThreePositioned.inheritedRouteSuffixesRoutes,
      dataLookup,
      PeriodicOneInThreePositioned.inheritedRouteSuffix,
      joinAtEndpoint,
      PositionedPeriodicCNF.orthogonalDetour]
  simpa
    [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      splitSource, sourcePlacement, inherited] using
    PeriodicOneInThreePositioned.splicedRoutes_length_ge_three_inherited
      splitSource sourcePlacement
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      inherited clauseMember literalMember
      sourceAtom literalSource inheritedLength

/-- Every wrapped coordinated route of a variable that reaches the third
occurrence slot has at least three listed points. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_length_ge_three_of_third
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
          (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
            source).erase
          atom .third = some sourceThird)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
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
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).length := by
  have genericThirdLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          ((PeriodicOneInThreePositioned.formula
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
              source)).rename WrappedPeriodicVariable.mk).erase
          atom .third = some sourceThird := by
    simpa
      [retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
        retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula]
      using thirdLookup
  rcases
      @PeriodicOneInThreePositioned.exists_original_of_wrapped_occurrenceAt_third
        (PeriodicPlanarThreeSATThreeVariable Variable)
        (inferInstance) (inferInstance) (inferInstance)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        atom sourceThird genericThirdLookup with
    ⟨sourceAtom, atomOriginal⟩
  rcases
      PositionedPeriodicCNF.exists_incidence_of_rename_members
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
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
    [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes]
    using
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_length_ge_three_of_original
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty rawClauseMember rawLiteralMember
        sourceAtom rawLiteralSource

/-- The coordinated unit-elimination splice preserves every terminal
direction needed by a degree-three wrapped Figure 9 variable. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PeriodicOneInThreeNoUnitsPositioned.PreservesDegreeThreeOriginalRouteTerminalDirections
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa
    [retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes]
    using
      PeriodicOneInThreeNoUnitsPositioned.preservesDegreeThreeOriginalRouteTerminalDirections_splicedRoutes
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty
              sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember).2.2)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember)
        (fun atom sourceThird thirdLookup
            _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember
            literalAtom =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_length_ge_three_of_third
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty atom sourceThird thirdLookup
            sourceClauseMember sourceLiteralMember literalAtom)

/-- The final coordinated unit-free route family meets variable incidences
in syntactic occurrence order clockwise. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
      (Classical.decEq _) (inferInstance)
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_preservesDegreeThreeOriginalRouteTerminalDirections
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes

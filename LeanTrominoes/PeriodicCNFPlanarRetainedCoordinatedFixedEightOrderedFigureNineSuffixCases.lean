/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PositionedPeriodicCNFLocalRouteSplicingEndpointDirections

/-!
# Pointwise cases for retained ordered Figure 9 suffixes

The completed two-stage suffix family has only two shapes.  A literal
inherited from the retained source receives the ordered connector-and-source
suffix selected by its recovered incidence metadata.  Either generation of
auxiliary receives the singleton local splice point.  These statements hide
the nested sum dispatch used to define the total family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance orderedSuffixCasesVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- A genuine twice-inherited literal exposes both its recovered source
incidence data and the exact ordered inherited suffix selected by the total
completed suffix family. -/
theorem
    retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (literalSource : literal.atom = .inl (.inl sourceAtom)) :
    ∃ data :
        PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex,
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          clauseIndex literalIndex = some data ∧
        (PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          (retainedFigureNineClearancePositionedFormula_widthAtMostThree
            source sourceWidth)
          (retainedFigureNineClearancePositionedFormula_allAtomsNodup
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty)).routes clauseIndex literalIndex =
          PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            (retainedFigureNineClearancePlacement source)
            data.sourceClause data.generatedClause
            (PositionedPeriodicCNF.clauseExitFanData
              data.sourceClause data.sourceClauseIndex
              (retainedFigureNineClearanceIncidenceRoutes source))
            (data.sourceSlot
              (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                source sourceWidth))
            (retainedFigureNineClearanceIncidenceRoutes
              source data.sourceClauseIndex data.sourceLiteralIndex) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let sourceRoutes := retainedFigureNineClearanceIncidenceRoutes source
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rcases
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  refine ⟨data, dataLookup, ?_⟩
  have completedShape :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes_routes_of_members
      clearanceSource clearancePlacement clearanceWidth clearanceDistinct
      original clauseMember literalMember
  rw [literalSource] at completedShape
  rw [completedShape]
  change
    PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes
        clearanceSource clearancePlacement clearanceWidth sourceRoutes
        clauseIndex literalIndex = _
  exact
    PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
      clearanceSource clearancePlacement clearanceWidth sourceRoutes
      clauseIndex literalIndex data dataLookup

/-- Every genuine literal that is not inherited from the retained source has
only the singleton local splice point as its completed suffix. -/
theorem
    retainedOrderedFixedEightCompleteRouteSuffixes_eq_singleton_of_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (notInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        literal.atom ≠ .inl (.inl sourceAtom)) :
    (PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)).routes clauseIndex literalIndex =
      [PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex literalIndex] := by
  rw [
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes_routes_of_members
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember]
  cases atomEq : literal.atom with
  | inl inherited =>
      cases inherited with
      | inl sourceAtom => exact (notInherited sourceAtom atomEq).elim
      | inr figureNineAuxiliary => simp
  | inr unitAuxiliary => simp

/-- A non-inherited incidence's complete retained route is exactly its
normalized local route, because its completed suffix is the singleton splice
point. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (notInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        literal.atom ≠ .inl (.inl sourceAtom)) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex =
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex literalIndex := by
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  have suffixSingleton :=
    retainedOrderedFixedEightCompleteRouteSuffixes_eq_singleton_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember notInherited
  change
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source))
        suffixes clauseIndex literalIndex = _
  exact
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes_eq_local_of_suffix_singleton
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source))
      suffixes clauseIndex literalIndex suffixSingleton

end PeriodicOrthocrossing
end LeanTrominoes

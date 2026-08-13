/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineClauseRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineMixedEndpointSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSuffixCases
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes
import LeanTrominoes.PeriodicGridDrawingLoopErasureRouteOrders

/-!
# Clause route order after final loop erasure

The raw composed Figure 9 routes already have the clause-side order needed
by the 3DM ribbon source.  Orthogonal loop erasure preserves that first edge
once the clause endpoint is known not to recur later in the subdivided raw
route.

For an auxiliary incidence the raw route is just its simple finite local
route.  For an inherited incidence, the second literal of the same ternary
clause is always auxiliary.  Its local route contains the common clause
endpoint and is strictly separated from the inherited suffix, proving that
the suffix cannot return to that endpoint.  The standard endpoint-isolated
join theorem then supplies the required freshness certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

local instance normalizedClauseOrderVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem polyline_length_ge_two_of_firstDirection_genuine
    {points : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection points).IsGenuine) :
    2 ≤ points.length := by
  cases points with
  | nil => simp [AxisDirection.polylineFirstDirection,
      AxisDirection.IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil => simp [AxisDirection.polylineFirstDirection,
          AxisDirection.IsGenuine] at genuine
      | cons second rest => simp

private theorem unitSubdividePolyline_length_ge_two_of_length_ge_two
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal : OrthogonalPolyline points) :
    2 ≤ (AxisDirection.unitSubdividePolyline points).length := by
  cases points with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          exact
            AxisDirection.unitSubdividePolyline_length_ge_two
              (first := first) (second := second)
              (rest := rest) orthogonal

private theorem normalize_firstDirection_eq_of_headNotInTail
    {points : List Cell} {direction : AxisDirection}
    (directionGenuine : direction.IsGenuine)
    (firstDirection :
      AxisDirection.polylineFirstDirection points = direction)
    (orthogonal : OrthogonalPolyline points)
    (fresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline points)) :
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline points) =
      direction := by
  have length : 2 ≤ points.length :=
    polyline_length_ge_two_of_firstDirection_genuine (by
      rw [firstDirection]
      exact directionGenuine)
  exact
    (AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
      (unitSubdividePolyline_length_ge_two_of_length_ge_two
        length orthogonal)
      orthogonal fresh).trans firstDirection

private theorem not_mem_right_of_mem_left_of_disjoint
    {α : Type*} {point : α} {left right : List α}
    (disjoint : List.Disjoint left right)
    (member : point ∈ left) :
    point ∉ right := by
  intro rightMember
  exact (List.disjoint_left.mp disjoint) member rightMember

/-- An inherited suffix cannot return to its clause vertex.  The second
literal of the same ternary clause is auxiliary, so its local route contains
the clause vertex and is strictly separated from the inherited suffix. -/
theorem
    retainedOrderedFixedEightCompleteRouteSuffixes_clausePoint_not_mem_of_inherited_ternary
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
    (arity : clause.literals.length = 3)
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
    let clearanceSource :=
      retainedFigureNineClearancePositionedFormula source
    let clearancePlacement := retainedFigureNineClearancePlacement source
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let clearanceDistinct :=
      retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
    let original :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
    let suffixes :=
      PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
        clearanceSource clearancePlacement clearanceWidth
        clearanceDistinct original
    PositionedPeriodicCNF.canonicalClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            clearanceSource clearancePlacement)
          clause ∉
      AxisDirection.unitSubdividePolyline
        (suffixes.routes clauseIndex literalIndex) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement := retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
  let suffix := suffixes.routes clauseIndex literalIndex
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom literalSource with
    ⟨data, _dataLookup, suffixShape⟩
  have suffixShape' :
      suffix =
        PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            clearanceSource clearancePlacement)
          clearancePlacement data.sourceClause data.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            data.sourceClause data.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (data.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex) := by
    simpa only [suffix, suffixes, clearanceSource, clearancePlacement,
      clearanceWidth, clearanceDistinct, original] using suffixShape
  rcases
      PlanarOneInThreeNoUnitsFigureNine.ternaryClause_secondLiteral_not_original
          clearanceSource clauseMember arity with
    ⟨secondLiteral, secondLiteralMember, secondNotInherited⟩
  let secondLocal :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex 1
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
          clearanceSource clauseMember with
    ⟨secondMetadata, secondMetadataLookup, _secondMetadataClause,
      _secondSourceMember, _secondEmbeddedMember⟩
  have secondStrictTranslated :=
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember secondLiteralMember
      secondNotInherited secondMetadata secondMetadataLookup
      data (0, 0)
  have zeroTranslation :
      (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        clearanceSource clearancePlacement).translation (0, 0) =
        (0, 0) := by
    simp [PeriodicVariablePlacement.translation, Cell.scale]
  dsimp only at secondStrictTranslated
  rw [zeroTranslation] at secondStrictTranslated
  have secondStrict :
      RoutesStrictlyAvoidEachOther secondLocal suffix := by
    rw [suffixShape']
    simpa only [PeriodicOrthocrossing.translatePolyline_zero]
      using secondStrictTranslated
  have secondOrthogonal : OrthogonalPolyline secondLocal := by
    simpa only [secondLocal] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
        clearanceSource clearancePlacement clearanceWidth
        clearanceDistinct clauseMember secondLiteralMember
  have suffixOrthogonal : OrthogonalPolyline suffix := by
    simpa only [suffix] using
      suffixes.orthogonal
        clause clauseIndex clauseMember literal literalIndex literalMember
  have subdivisionsDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline secondLocal)
        (AxisDirection.unitSubdividePolyline suffix) :=
    secondStrict.unitSubdividePolyline_disjoint
      secondOrthogonal suffixOrthogonal
  have secondHead :
      secondLocal.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              clearanceSource clearancePlacement)
            clause) := by
    simpa only [secondLocal] using
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clauseMember secondLiteralMember).1
  have secondNonempty : secondLocal ≠ [] := by
    intro empty
    rw [empty] at secondHead
    simp at secondHead
  have clausePointInSecond :
      PositionedPeriodicCNF.canonicalClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            clearanceSource clearancePlacement)
          clause ∈
        AxisDirection.unitSubdividePolyline secondLocal := by
    apply List.mem_of_mem_head?
    rw [AxisDirection.unitSubdividePolyline_head? secondNonempty]
    rw [secondHead]
    simp
  exact
    not_mem_right_of_mem_left_of_disjoint
      subdivisionsDisjoint clausePointInSecond

/-- Every genuine ternary raw route has an isolated clause endpoint after
ordered unit subdivision. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_headNotInTail_of_ternary
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
    (arity : clause.literals.length = 3)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex)) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement := retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex literalIndex
  let rawRoute :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseIndex literalIndex
  have localEndpointsRaw :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth clearanceDistinct
      clauseMember literalMember
  have localHead :
      localRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              clearanceSource clearancePlacement)
            clause) := by
    simpa only [localRoute] using localEndpointsRaw.1
  have localLast :
      localRoute.getLast? =
        some
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
            clearanceSource clearancePlacement clauseIndex literalIndex) := by
    simpa only [localRoute] using localEndpointsRaw.2
  clear localEndpointsRaw
  have localOrthogonal : OrthogonalPolyline localRoute := by
    simpa only [localRoute] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clauseMember literalMember
  have localSimple : LocalIncidenceDrawing.RouteIsSimple localRoute := by
    simpa only [localRoute] using
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_isSimple_of_members
        clearanceSource clearancePlacement clearanceWidth clearanceDistinct
        clauseMember literalMember
  have localFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline localRoute) :=
    AxisDirection.headNotInTail_unitSubdividePolyline_of_simple
      localOrthogonal localSimple
  rcases atomEq : literal.atom with outerInherited | unitAuxiliary
  · rcases figureAtomEq : outerInherited with sourceAtom | figureAuxiliary
    · have literalSource : literal.atom = .inl (.inl sourceAtom) := by
        simp [atomEq, figureAtomEq]
      let suffix := suffixes.routes clauseIndex literalIndex
      have clausePointNotInSuffix :
          PositionedPeriodicCNF.canonicalClausePosition
              (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
                clearanceSource clearancePlacement)
              clause ∉
            AxisDirection.unitSubdividePolyline suffix := by
        simpa only [suffix, suffixes, clearanceSource,
          clearancePlacement, clearanceWidth, clearanceDistinct,
          original] using
          retainedOrderedFixedEightCompleteRouteSuffixes_clausePoint_not_mem_of_inherited_ternary
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember arity literalMember
            sourceAtom literalSource
      have localNonempty : localRoute ≠ [] := by
        intro empty
        rw [empty] at localHead
        simp at localHead
      have suffixHead :
          suffix.head? =
            some
              (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
                clearanceSource clearancePlacement
                clauseIndex literalIndex) := by
        simpa only [suffix] using
          (suffixes.endpoints
            clause clauseIndex clauseMember literal literalIndex
            literalMember).1
      have joined :=
        AxisDirection.HeadNotInTail.unitSubdividePolyline_joinAtEndpoint
          localFresh localNonempty localHead localLast
          suffixHead clausePointNotInSuffix
      change
        AxisDirection.HeadNotInTail
          (AxisDirection.unitSubdividePolyline
            (LeanTrominoes.joinAtEndpoint localRoute suffix))
      exact joined
    · have notInherited :
          ∀ sourceAtom :
              ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable),
            literal.atom ≠ .inl (.inl sourceAtom) := by
        intro sourceAtom equal
        simp [atomEq, figureAtomEq] at equal
      rw [retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember notInherited]
      exact localFresh
  · have notInherited :
        ∀ sourceAtom :
            ThreeOccurrenceVariable
              (WrappedPeriodicPlanarSATVariable Variable),
          literal.atom ≠ .inl (.inl sourceAtom) := by
      intro sourceAtom equal
      simp [atomEq] at equal
    rw [retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember notInherited]
    exact localFresh

/-- Final loop erasure preserves the canonical first direction of one tagged
ternary-clause incidence. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_tagged_ternary
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (indexed :
      CNFIncidence
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)) ×
        Nat)
    (indexedMember :
      indexed ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.incidencesWithMetadata.zipIdx)
    (arity : indexed.1.clause.length = 3) :
    AxisDirection.polylineFirstDirection
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty indexed.1.clauseIndex
          indexed.1.literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection
        indexed.1.literalIndex := by
  let formula :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source
  let routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let rawRoute :=
    routes indexed.1.clauseIndex indexed.1.literalIndex
  have rawOrdered :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have rawDirection :
      AxisDirection.polylineFirstDirection rawRoute =
        AxisDirection.unitEliminationClauseExitDirection
          indexed.1.literalIndex := by
    simpa only [rawRoute, routes] using
      rawOrdered indexed indexedMember arity
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      formula indexedMember with
    ⟨clause, literal, clauseMember, literalMember, incidenceEqual⟩
  have clauseLiteralsEqual : indexed.1.clause = clause.literals := by
    simpa using congrArg (fun incidence => incidence.clause) incidenceEqual
  have clauseArity : clause.literals.length = 3 := by
    rw [← clauseLiteralsEqual]
    exact arity
  have routeOrthogonal : OrthogonalPolyline rawRoute := by
    simpa only [rawRoute, routes] using
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2
  have routeFresh :
      AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline rawRoute) := by
    simpa only [rawRoute, routes] using
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_headNotInTail_of_ternary
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember clauseArity literalMember
  have normalizedDirection :=
    normalize_firstDirection_eq_of_headNotInTail
      (AxisDirection.unitEliminationClauseExitDirection_isGenuine
        indexed.1.literalIndex)
      rawDirection routeOrthogonal routeFresh
  rw [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_eq_normalize]
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline rawRoute) = _
  exact normalizedDirection

/-- The normalized retained Figure 9 routes retain the canonical
ternary-clause exit order through endpoint-isolated loop erasure. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.TernaryClauseRoutesInUnitEliminationOrder
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  intro indexed indexedMember arity
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_firstDirection_of_tagged_ternary
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty indexed indexedMember arity

end PeriodicOrthocrossing
end LeanTrominoes

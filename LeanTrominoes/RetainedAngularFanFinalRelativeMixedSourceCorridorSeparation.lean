import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSourceSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedAlignedCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedComponentCorridorReduction
import LeanTrominoes.RetainedFinalRouteCommonFrameBoundaries
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Relative mixed retained-source corridors

Periodic retained-source planarity permits contacts only at advertised route
endpoints.  At a nonzero relative period shift, the clause endpoints differ;
when the canonical literal endpoints differ as well, all four endpoint pairs
are distinct.  Thus the complete raw routes are strictly separated.  For an
aligned successful direct choice and an orthogonal failed-choice route, this
strict certificate supplies the exact translated source corridor used by the
final Figure 7 boundary assembly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- If translating `second` forward would make it equal to `first`, then
translating `first` backward would make it equal to `second`. -/
private theorem point_ne_translated_of_reverse_ne
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (first second relativeTranslate : Cell)
    (reverseNe :
      second ≠
        Cell.add first
          (placement.translation (Cell.neg relativeTranslate))) :
    first ≠
      Cell.add (placement.translation relativeTranslate) second := by
  intro equal
  apply reverseNe
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases relativeTranslate with ⟨translateX, translateY⟩
  simp [PeriodicVariablePlacement.translation,
    Cell.neg, Cell.sub, Cell.add, Cell.scale] at equal ⊢
  omega

/-- At a nonzero relative shift, two retained source routes with different
canonical literal endpoints are completely contact-free. -/
theorem
    finalCoordinatedSourceRoutes_strictlyAvoid_translated_of_nonzero_of_distinctCenters
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let firstRoute := routes firstClauseIndex firstLiteralIndex
  let secondRoute := routes secondClauseIndex secondLiteralIndex
  let translatedSecondRoute :=
    translatePolyline
      (placement.translation relativeTranslate) secondRoute
  have occurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate) := by
    intro equal
    apply relativeTranslateNonzero
    exact (congrArg Prod.snd equal).symm
  have sourceRelative :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_relativeAvoidEachOther
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have sourceCoordinate :=
    @PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther.coordinate
      (WrappedPeriodicPlanarSATVariable Variable)
      (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
        Variable inferInstance)
      _ _ _ sourceRelative
  have rawAvoid :
      RoutesAvoidEachOther firstRoute translatedSecondRoute := by
    simpa [source, placement, routes, firstRoute, secondRoute,
      translatedSecondRoute, finalCoordinatedSource,
      finalCoordinatedPlacement, finalCoordinatedSourceRoutes,
      translatePolyline] using
      sourceCoordinate
        firstClause firstClauseIndex firstClauseMember
        firstLiteral firstLiteralIndex firstLiteralMember
        secondClause secondClauseIndex secondClauseMember
        secondLiteral secondLiteralIndex secondLiteralMember
        relativeTranslate occurrencesDifferent
  have firstEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSecondHead :
      translatedSecondRoute.head? =
        some
          (Cell.add (placement.translation relativeTranslate)
            (PositionedPeriodicCNF.canonicalClausePosition
              placement secondClause)) := by
    simp [translatedSecondRoute, translatePolyline,
      secondRoute, routes, placement, secondEndpoints.1]
  have translatedSecondLast :
      translatedSecondRoute.getLast? =
        some
          (Cell.add (placement.translation relativeTranslate)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement secondClause secondLiteral)) := by
    simp [translatedSecondRoute, translatePolyline,
      secondRoute, routes, placement, secondEndpoints.2]
  have secondTaggedMember :
      (secondLiteral, secondClauseIndex, secondLiteralIndex) ∈
        taggedLiterals source.erase :=
    taggedLiteral_mem_of_positioned_members
      source secondClauseMember secondLiteralMember
  have secondAtomMember :
      secondLiteral.atom ∈ sourceVariables source.erase :=
    sourceVariables_mem source.erase secondTaggedMember
  have firstTaggedMember :
      (firstLiteral, firstClauseIndex, firstLiteralIndex) ∈
        taggedLiterals source.erase :=
    taggedLiteral_mem_of_positioned_members
      source firstClauseMember firstLiteralMember
  have firstAtomMember :
      firstLiteral.atom ∈ sourceVariables source.erase :=
    sourceVariables_mem source.erase firstTaggedMember
  have headHeadPointsNe :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstClause ≠
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondClause) := by
    have distinct :=
      finalCoordinatedCanonicalClausePositions_ne_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        relativeTranslate relativeTranslateNonzero
    simpa [placement, Cell.add, add_comm] using distinct
  have headLastPointsNe :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstClause ≠
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement secondClause secondLiteral) := by
    have distinct :=
      finalCoordinatedCanonicalClausePosition_ne_translatedSourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
        secondLiteral.atom secondAtomMember
        (Cell.add
          (incidenceRelativeOffset secondClause secondLiteral)
          relativeTranslate)
    rw [← canonicalLiteralPosition_add_translation_eq_atomPosition_translation
      placement secondClause secondLiteral relativeTranslate] at distinct
    simpa [Cell.add, add_comm] using distinct
  have reverseLastHeadPointsNe :
      PositionedPeriodicCNF.canonicalClausePosition
          placement secondClause ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral)
          (placement.translation (Cell.neg relativeTranslate)) := by
    have distinct :=
      finalCoordinatedCanonicalClausePosition_ne_translatedSourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        firstLiteral.atom firstAtomMember
        (Cell.add
          (incidenceRelativeOffset firstClause firstLiteral)
          (Cell.neg relativeTranslate))
    rw [← canonicalLiteralPosition_add_translation_eq_atomPosition_translation
      placement firstClause firstLiteral
      (Cell.neg relativeTranslate)] at distinct
    exact distinct
  have lastHeadPointsNe :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral ≠
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondClause) :=
    point_ne_translated_of_reverse_ne
      placement
      (PositionedPeriodicCNF.canonicalLiteralPosition
        placement firstClause firstLiteral)
      (PositionedPeriodicCNF.canonicalClausePosition
        placement secondClause)
      relativeTranslate reverseLastHeadPointsNe
  have lastLastPointsNe :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral ≠
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement secondClause secondLiteral) := by
    simpa [placement, Cell.add, add_comm] using centersDifferent
  apply
    routesStrictlyAvoidEachOther_of_avoid_of_endpoints_ne rawAvoid
  · rw [show firstRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement firstClause) by
          simpa [firstRoute, routes, placement] using firstEndpoints.1,
      translatedSecondHead]
    exact fun equal => headHeadPointsNe (Option.some.inj equal)
  · rw [show firstRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement firstClause) by
          simpa [firstRoute, routes, placement] using firstEndpoints.1,
      translatedSecondLast]
    exact fun equal => headLastPointsNe (Option.some.inj equal)
  · rw [show firstRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral) by
          simpa [firstRoute, routes, placement] using firstEndpoints.2,
      translatedSecondHead]
    exact fun equal => lastHeadPointsNe (Option.some.inj equal)
  · rw [show firstRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral) by
          simpa [firstRoute, routes, placement] using firstEndpoints.2,
      translatedSecondLast]
    exact fun equal => lastLastPointsNe (Option.some.inj equal)

/-- The translated failed-choice source prefix has the exact mixed corridor
against an aligned successful direct route. -/
theorem
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_directSegment_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    SourcePrefixCorridorSeparated
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex))
      (finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let directRoute :=
    routes directClauseIndex directLiteralIndex
  let fallbackRoute :=
    routes fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      (placement.translation relativeTranslate) fallbackRoute
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackLength : 2 ≤ fallbackRoute.length := by
    simpa [fallbackRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackLength :
      2 ≤ translatedFallbackRoute.length := by
    simpa [translatedFallbackRoute, translatePolyline] using fallbackLength
  have directOrthogonal : OrthogonalPolyline directRoute := by
    simpa [directRoute, routes] using
      retainedFinalDirectSourceRoute_orthogonal_of_sourceSegment_axisAligned
        formula directClauseIndex directLiteralIndex
        choice choiceLookup directAligned
  have fallbackOrthogonal : OrthogonalPolyline fallbackRoute := by
    simpa [fallbackRoute, routes] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember
        fallbackLiteralMember fallbackChoiceNone
  have translatedFallbackOrthogonal :
      OrthogonalPolyline translatedFallbackRoute := by
    exact fallbackOrthogonal.translate
      (placement.translation relativeTranslate)
  have directRetained : RetainedRayPolyline directRoute := by
    simpa [directRoute, routes, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackRetained : RetainedRayPolyline fallbackRoute := by
    simpa [fallbackRoute, routes, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackRetained :
      RetainedRayPolyline translatedFallbackRoute := by
    exact fallbackRetained.translate
      (placement.translation relativeTranslate)
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) =
        some directTerminal := by
    simpa only [directRoute, directTerminal, routes] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have strict :=
    finalCoordinatedSourceRoutes_strictlyAvoid_translated_of_nonzero_of_distinctCenters
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      relativeTranslate relativeTranslateNonzero centersDifferent
  have prefixStrict :
      RoutesStrictlyAvoidEachOther
        translatedFallbackRoute.dropLast directRoute := by
    simpa [directRoute, fallbackRoute, translatedFallbackRoute,
      routes, placement] using strict.symm.dropLast_left
  have rectangles :
      SourcePolylineRectanglesSeparated
        translatedFallbackRoute.dropLast directRoute :=
    SourcePolylineRectanglesSeparated.of_strictlyAvoid
      translatedFallbackOrthogonal.dropLast directOrthogonal prefixStrict
  change
    SourcePrefixCorridorSeparated
      translatedFallbackRoute directRoute directTerminal.1
  exact
    sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
      translatedFallbackRoute directRoute directTerminal
      translatedFallbackRetained directRetained
      translatedFallbackLength directLength directClassified rectangles

/-- At a nonzero shift, deleting the translated second route's final point
strictly separates that prefix from the complete first route, even when the
two final endpoints coincide. -/
theorem
    finalCoordinatedTranslatedSecondSourceRoutePrefix_strictlyAvoids_firstSourceRoute_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)).dropLast
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let firstRoute := routes firstClauseIndex firstLiteralIndex
  let secondRoute := routes secondClauseIndex secondLiteralIndex
  let translatedSecondRoute :=
    translatePolyline
      (placement.translation relativeTranslate) secondRoute
  have firstLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have rawAvoid :
      RoutesAvoidEachOther firstRoute translatedSecondRoute := by
    simpa [firstRoute, secondRoute, translatedSecondRoute,
      routes, placement] using
      finalCoordinatedSourceRoutes_avoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero
  have prefixesAvoid :
      RoutesStrictlyAvoidEachOther
        translatedSecondRoute.dropLast firstRoute.dropLast := by
    simpa [firstRoute, secondRoute, translatedSecondRoute,
      routes, placement] using
      (finalCoordinatedSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero).symm
  have secondNodup : secondRoute.Nodup := by
    simpa [source, routes, secondRoute,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty
        (secondClause, secondClauseIndex)
        (by simpa [source, finalCoordinatedSource] using secondClauseMember)
        (secondLiteral, secondLiteralIndex) secondLiteralMember).1
  have translatedSecondNodup : translatedSecondRoute.Nodup := by
    exact secondNodup.map
      (Cell.add_left_injective (placement.translation relativeTranslate))
  have firstEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSecondHead :
      translatedSecondRoute.head? =
        some
          (Cell.add (placement.translation relativeTranslate)
            (PositionedPeriodicCNF.canonicalClausePosition
              placement secondClause)) := by
    simp [translatedSecondRoute, translatePolyline,
      secondRoute, routes, placement, secondEndpoints.1]
  have firstTaggedMember :
      (firstLiteral, firstClauseIndex, firstLiteralIndex) ∈
        taggedLiterals source.erase :=
    taggedLiteral_mem_of_positioned_members
      source firstClauseMember firstLiteralMember
  have firstAtomMember :
      firstLiteral.atom ∈ sourceVariables source.erase :=
    sourceVariables_mem source.erase firstTaggedMember
  have reverseSourceNe :
      PositionedPeriodicCNF.canonicalClausePosition
          placement secondClause ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral)
          (placement.translation (Cell.neg relativeTranslate)) := by
    have distinct :=
      finalCoordinatedCanonicalClausePosition_ne_translatedSourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        firstLiteral.atom firstAtomMember
        (Cell.add
          (incidenceRelativeOffset firstClause firstLiteral)
          (Cell.neg relativeTranslate))
    rw [← canonicalLiteralPosition_add_translation_eq_atomPosition_translation
      placement firstClause firstLiteral
      (Cell.neg relativeTranslate)] at distinct
    exact distinct
  have firstTargetNeTranslatedSecondSource :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral ≠
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondClause) :=
    point_ne_translated_of_reverse_ne
      placement
      (PositionedPeriodicCNF.canonicalLiteralPosition
        placement firstClause firstLiteral)
      (PositionedPeriodicCNF.canonicalClausePosition
        placement secondClause)
      relativeTranslate reverseSourceNe
  have translatedSecondSourceNeFirstTarget :
      Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondClause) ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral :=
    Ne.symm firstTargetNeTranslatedSecondSource
  have translatedSecondPrefixAvoidsFirstTarget :=
    routePrefix_avoids_other_final_point_of_avoid
      (routesAvoidEachOther_comm rawAvoid)
      translatedSecondNodup translatedSecondHead
      (by
        simpa [firstRoute, routes, placement] using firstEndpoints.2)
      translatedSecondSourceNeFirstTarget
  have firstEntrance :
      firstRoute.dropLast.getLast? =
        some (polylineLastEntrance firstRoute) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec
        (exists_reverse_tail_head?_of_two_le_length
          firstRoute firstLength))
  have finalSegmentAvoid :
      RoutesStrictlyAvoidEachOther translatedSecondRoute.dropLast
        [polylineLastEntrance firstRoute,
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral] :=
    routesStrictlyAvoidEachOther_dropLast_finalSegment
      (routesAvoidEachOther_comm rawAvoid)
      prefixesAvoid firstEntrance
      (by simpa [firstRoute, routes, placement] using firstEndpoints.2)
      translatedSecondPrefixAvoidsFirstTarget.1
  have joined :=
    prefixesAvoid.join_right finalSegmentAvoid firstEntrance (by simp)
  have decomposition :
      firstRoute.dropLast ++
          [PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral] = firstRoute :=
    List.dropLast_append_getLast?
      (PositionedPeriodicCNF.canonicalLiteralPosition
        placement firstClause firstLiteral)
      (by simpa [firstRoute, routes, placement] using firstEndpoints.2)
  simpa [firstRoute, secondRoute, translatedSecondRoute,
    routes, placement, joinAtEndpoint, decomposition] using joined

/-- The translated failed-choice source prefix has the exact corridor
against an aligned successful direct route at every nonzero shift, including
the shared-target case. -/
theorem
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_directSegment_axisAligned_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    SourcePrefixCorridorSeparated
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex))
      (finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      (placement.translation relativeTranslate) fallbackRoute
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackLength : 2 ≤ fallbackRoute.length := by
    simpa [fallbackRoute, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackLength :
      2 ≤ translatedFallbackRoute.length := by
    simpa [translatedFallbackRoute, translatePolyline] using fallbackLength
  have directOrthogonal : OrthogonalPolyline directRoute := by
    simpa [directRoute] using
      retainedFinalDirectSourceRoute_orthogonal_of_sourceSegment_axisAligned
        formula directClauseIndex directLiteralIndex
        choice choiceLookup directAligned
  have fallbackOrthogonal : OrthogonalPolyline fallbackRoute := by
    simpa [fallbackRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember
        fallbackLiteralMember fallbackChoiceNone
  have translatedFallbackOrthogonal :
      OrthogonalPolyline translatedFallbackRoute :=
    fallbackOrthogonal.translate (placement.translation relativeTranslate)
  have directRetained : RetainedRayPolyline directRoute := by
    simpa [directRoute, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackRetained : RetainedRayPolyline fallbackRoute := by
    simpa [fallbackRoute, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackRetained :
      RetainedRayPolyline translatedFallbackRoute :=
    fallbackRetained.translate (placement.translation relativeTranslate)
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) = some directTerminal := by
    simpa only [directRoute, directTerminal] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have prefixStrict :
      RoutesStrictlyAvoidEachOther
        translatedFallbackRoute.dropLast directRoute := by
    simpa [directRoute, fallbackRoute, translatedFallbackRoute,
      placement] using
      finalCoordinatedTranslatedSecondSourceRoutePrefix_strictlyAvoids_firstSourceRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate relativeTranslateNonzero
  have rectangles :
      SourcePolylineRectanglesSeparated
        translatedFallbackRoute.dropLast directRoute :=
    SourcePolylineRectanglesSeparated.of_strictlyAvoid
      translatedFallbackOrthogonal.dropLast directOrthogonal prefixStrict
  change
    SourcePrefixCorridorSeparated
      translatedFallbackRoute directRoute directTerminal.1
  exact
    sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
      translatedFallbackRoute directRoute directTerminal
      translatedFallbackRetained directRetained
      translatedFallbackLength directLength directClassified rectangles

/-- At every nonzero relative shift, the translated failed-choice source
prefix has the exact refined terminal corridor against an arbitrary successful
direct route.  The only non-rectangular component case is an overlapping
carrier lens, where the common-frame carrier boundary supplies the corridor
checkpoint separation. -/
theorem
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    SourcePrefixCorridorSeparated
      (translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex))
      (finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  apply
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_componentCases
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone relativeTranslate
  intro fallbackCarrier directMacrocell rectanglesNotSeparated
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      fallbackRoute
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  have directOccurrenceEq :
      finalGaugedRouteOccurrence
          formula directClauseIndex directLiteralIndex (0, 0) =
        directRoute := by
    exact
      (finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
        formula directClauseIndex directLiteralIndex).symm
  have fallbackOccurrenceEq :
      finalGaugedRouteOccurrence
          formula fallbackClauseIndex fallbackLiteralIndex
            relativeTranslate =
        translatedFallbackRoute := by
    rfl
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) =
        some directTerminal := by
    simpa [directRoute, directTerminal] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have directComponent :
      directMacrocell.metadata.source.component.IsDirect :=
    directMacrocell.toFinalGaugedRouteOccurrenceWitness
      |>.componentIsDirect_of_finalChoiceSome
        formula choice choiceLookup
  rcases
      fallbackCarrier.exists_carrierBoundary_of_direct_of_notSeparated
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        directMacrocell directComponent rectanglesNotSeparated with
    ⟨boundary⟩
  have prefixStrict :
      RoutesStrictlyAvoidEachOther
        translatedFallbackRoute.dropLast directRoute := by
    simpa [directRoute, fallbackRoute, translatedFallbackRoute] using
      finalCoordinatedTranslatedSecondSourceRoutePrefix_strictlyAvoids_firstSourceRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate relativeTranslateNonzero
  change
    SourcePrefixCorridorSeparated
      translatedFallbackRoute directRoute directTerminal.1
  rw [← fallbackOccurrenceEq, ← directOccurrenceEq]
  apply
    sourcePrefixCorridorSeparated_of_outside_insideCarrierBoundary
      boundary.port boundary.origin
      (finalGaugedRouteOccurrence
        formula fallbackClauseIndex fallbackLiteralIndex relativeTranslate)
      (finalGaugedRouteOccurrence
        formula directClauseIndex directLiteralIndex (0, 0))
      directTerminal
      (by simpa [directOccurrenceEq] using directLength)
      (by simpa [directOccurrenceEq] using directClassified)
  · intro point pointMember
    exact boundary.carrierOutside point pointMember
  · exact boundary.macrocellInside
  · simpa [fallbackOccurrenceEq, directOccurrenceEq] using prefixStrict

end PeriodicOrthocrossing
end LeanTrominoes

import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVertexPositions
import LeanTrominoes.RetainedFinalFlatCorridorComponentCases
import LeanTrominoes.RetainedFinalFlatNormalizedCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackMacrocellSeparation

/-!
# Source corridors for oblique final mixed pairs

When a successful direct source segment is oblique, the flat route
decomposition reduces its interaction with a failed fallback prefix to two
local residues.  Normalized carrier geometry closes an overlapping carrier
prefix, while flat-list index recovery identifies an equal macrocell with
the failed choice and contradicts direct-component choice completeness.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 800000

private theorem localRoute_terminalClassify :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length),
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (retainedDirectSourceLocalRouteAt kind index)) =
        some (retainedDirectSourceLocalTerminalAt kind index) := by
  native_decide

private theorem prefixChoice_direction_eq_localTerminal
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    (retainedDirectSourcePrefixChoiceAt kind index).direction =
      (retainedDirectSourceLocalTerminalAt kind index).1 := by
  have equal :=
    congrArg Prod.fst
      (retainedDirectSourceFanTerminalAt_eq_scale kind index)
  simpa [retainedDirectSourceFanTerminalAt,
    scaleRetainedTerminalData] using equal

private theorem directChoice_terminalClassify
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice) :
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)) =
      some
        ((retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1,
          (retainedDirectSourceLocalTerminalAt
            choice.kind choice.index).2) := by
  have represents :=
    retainedFinalDirectSourceRouteChoice_representsFinalRoute
      formula clauseIndex literalIndex choice choiceLookup
  unfold RetainedDirectSourceRouteChoice.RepresentsFinalRoute at represents
  have localClassified :=
    localRoute_terminalClassify
      choice.kind choice.index
  have representedClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex)) =
        some (retainedDirectSourceLocalTerminalAt
          choice.kind choice.index) := by
    change retainedTerminalDirectionClassify
        (routeTerminalVector
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula clauseIndex literalIndex)) = _
    rw [← represents, routeTerminalVector_translatePolyline]
    exact localClassified
  simpa [retainedDirectSourceFanTerminalAt,
    prefixChoice_direction_eq_localTerminal]
    using representedClassified

private theorem canonicalClausePositions_ne_of_nodup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (positionsNodup :
      (source.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          placement)).Nodup)
    {firstClause secondClause : PositionedPeriodicClause Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈ source.clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈ source.clauses.zipIdx)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    PositionedPeriodicCNF.canonicalClausePosition
        placement firstClause ≠
      PositionedPeriodicCNF.canonicalClausePosition
        placement secondClause := by
  have firstLookup :
      source.clauses[firstClauseIndex]? = some firstClause :=
    (List.mem_zipIdx_iff_getElem?).mp firstClauseMember
  have secondLookup :
      source.clauses[secondClauseIndex]? = some secondClause :=
    (List.mem_zipIdx_iff_getElem?).mp secondClauseMember
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstIndexLt, firstAt⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondIndexLt, secondAt⟩
  intro positionsEqual
  have firstMapIndexLt :
      firstClauseIndex <
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition
            placement)).length := by
    simpa using firstIndexLt
  have secondMapIndexLt :
      secondClauseIndex <
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition
            placement)).length := by
    simpa using secondIndexLt
  have mappedPositionsEqual :
      (source.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition placement))[
          firstClauseIndex]'firstMapIndexLt =
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition placement))[
            secondClauseIndex]'secondMapIndexLt := by
    simp only [List.getElem_map]
    rw [firstAt, secondAt]
    exact positionsEqual
  apply clauseIndicesDifferent
  exact
    (positionsNodup.getElem_inj_iff
      (hi := firstMapIndexLt)
      (hj := secondMapIndexLt)).mp mappedPositionsEqual

private theorem finalCanonicalClausePositions_ne
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
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) firstClause ≠
      PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) secondClause := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have retainedClausesNonempty :
      ∀ retainedClause ∈ retainedDrawingPlanarSATFormula formula,
        retainedClause.literals ≠ [] :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have positionsNodup :
      ((finalCoordinatedSource formula).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (finalCoordinatedPlacement formula))).Nodup := by
    change
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula))).Nodup
    exact
      deduplicated_canonicalClausePositions_nodup
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  exact
    canonicalClausePositions_ne_of_nodup
      (finalCoordinatedSource formula)
      (finalCoordinatedPlacement formula)
      positionsNodup firstClauseMember secondClauseMember
      clauseIndicesDifferent

/-- Recovering a failed macrocell's flat incidence tag identifies its checked
choice indices, so the abstract failed-choice macrocell separation applies. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_incidence_choice_none_of_second_finalSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {failedRoute referenceRoute : List Cell}
    {failedIndex referenceIndex : Nat}
    (failed :
      FinalGaugedFlatRouteMacrocellWitness
        formula (failedRoute, failedIndex))
    (reference :
      FinalGaugedFlatRouteMacrocellWitness
        formula (referenceRoute, referenceIndex))
    {failedClauseIndex failedLiteralIndex : Nat}
    {failedClause :
      List (PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable))}
    {failedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    (failedIncidenceMember :
      ((⟨failedClauseIndex, failedClause,
          failedLiteralIndex, failedLiteral⟩ :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable)),
        failedIndex) ∈
          (finalGaugedIncidences formula).zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failedClauseIndex failedLiteralIndex = none)
    (referenceLength : 2 ≤ referenceRoute.length)
    {referenceTarget : Cell}
    (referenceLast : referenceRoute.getLast? = some referenceTarget)
    (referenceOblique :
      ¬(⟨polylineLastEntrance referenceRoute,
          referenceTarget⟩ : GridSegment).IsAxisAligned) :
    failed.translatedCenter ≠ reference.translatedCenter := by
  have taggedIncidenceEq :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      failed.coordinates.finalIncidenceMember
      failedIncidenceMember
      failed.coordinates.finalIncidenceIndexEq
  have clauseIndexEq :
      failed.coordinates.taggedClause.2 = failedClauseIndex :=
    failed.coordinates.taggedClauseIndexEq.trans
      (congrArg
        (fun taggedIncidence :
            CNFIncidence
                (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
          taggedIncidence.1.clauseIndex)
        taggedIncidenceEq)
  have literalIndexEq :
      failed.coordinates.taggedLiteral.2 = failedLiteralIndex :=
    failed.coordinates.taggedLiteralIndexEq.trans
      (congrArg
        (fun taggedIncidence :
            CNFIncidence
                (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
          taggedIncidence.1.literalIndex)
        taggedIncidenceEq)
  have recoveredChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failed.coordinates.taggedClause.2
            failed.coordinates.taggedLiteral.2 = none := by
    rw [clauseIndexEq, literalIndexEq]
    exact choiceNone
  exact
    FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_choice_none_of_second_finalSegment_not_axisAligned
      (formula := formula) wellFormed degree isLocal
      (failedTaggedRoute := (failedRoute, failedIndex))
      (referenceTaggedRoute := (referenceRoute, referenceIndex))
      (failed := failed) (reference := reference)
      (choiceNone := recoveredChoiceNone)
      (referenceLength := referenceLength)
      (referenceTarget := referenceTarget)
      (referenceLast := referenceLast)
      (referenceOblique := referenceOblique)

/-- A cross-clause source prefix has the required corridor against every
successful oblique direct source segment when its own checked choice fails. -/
theorem
    retainedFinalDirectFallback_sourcePrefixCorridorSeparated_of_directSegment_not_axisAligned
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
          formula directClauseIndex directLiteralIndex =
        some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (directOblique :
      ¬(⟨polylineLastEntrance
            (finalCoordinatedSourceRoutes
              formula directClauseIndex directLiteralIndex),
          (finalCoordinatedSourceRoutes
            formula directClauseIndex directLiteralIndex).getLastD
              (0, 0)⟩ : GridSegment).IsAxisAligned) :
    SourcePrefixCorridorSeparated
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
      (finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 := by
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
  let directRoute :=
    routes directClauseIndex directLiteralIndex
  let fallbackRoute :=
    routes fallbackClauseIndex fallbackLiteralIndex
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  have copiesDifferent :
      (directLiteral.atom, directClauseIndex, directLiteralIndex) ≠
        (fallbackLiteral.atom, fallbackClauseIndex, fallbackLiteralIndex) := by
    intro copiesEqual
    apply clauseIndicesDifferent
    exact congrArg (fun copy => copy.2.1) copiesEqual
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        directClauseMember directLiteralMember with
    ⟨directRouteIndex, directIncidenceMember, directRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        fallbackClauseMember fallbackLiteralMember with
    ⟨fallbackRouteIndex, fallbackIncidenceMember, fallbackRouteMember⟩
  have routeIndicesDifferent :
      fallbackRouteIndex ≠ directRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        fallbackIncidenceMember directIncidenceMember indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    exact
      (congrArg
        (fun incidence :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual).symm
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
  have directEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directLast :
      directRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral) := by
    exact directEndpoints.2
  have fallbackHead :
      fallbackRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement fallbackClause) := by
    exact fallbackEndpoints.1
  have compatible :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have fallbackHeadNeDirectLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable inferInstance firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _ fallbackIncidenceMember directIncidenceMember
  have sourcesDifferent :=
    finalCanonicalClausePositions_ne
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      fallbackClauseMember directClauseMember
      (Ne.symm clauseIndicesDifferent)
  have headsDifferent : fallbackRoute.head? ≠ directRoute.head? := by
    rw [show fallbackRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement fallbackClause) by
          simpa [fallbackRoute, routes, placement] using
            fallbackEndpoints.1,
      show directRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement directClause) by
          simpa [directRoute, routes, placement] using
            directEndpoints.1]
    exact fun equal => sourcesDifferent (Option.some.inj equal)
  have fallbackSourceNeDirectTarget :
      PositionedPeriodicCNF.canonicalClausePosition
          placement fallbackClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement directClause directLiteral := by
    rw [fallbackEndpoints.1, directEndpoints.2]
      at fallbackHeadNeDirectLast
    simpa [fallbackRoute, directRoute, routes] using
      fallbackHeadNeDirectLast
  have fallbackRetained : RetainedRayPolyline fallbackRoute := by
    simpa [fallbackRoute, routes, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directRetained : RetainedRayPolyline directRoute := by
    simpa [directRoute, routes, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) =
        some directTerminal := by
    simpa only [directRoute, directTerminal, routes] using
      directChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have directLastD :
      directRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement directClause directLiteral := by
    rw [List.getLastD_eq_getLast?, directLast]
    rfl
  have directFinalOblique :
      ¬(⟨polylineLastEntrance directRoute,
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral⟩ :
        GridSegment).IsAxisAligned := by
    have directRouteOblique :
        ¬(⟨polylineLastEntrance directRoute,
            directRoute.getLastD (0, 0)⟩ :
          GridSegment).IsAxisAligned := by
      simpa only [directRoute, routes] using directOblique
    rw [directLastD] at directRouteOblique
    exact directRouteOblique
  rw [show
    finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex =
      fallbackRoute from rfl]
  rw [show
    finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex =
      directRoute from rfl]
  rw [show
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 =
      directTerminal.1 from rfl]
  apply
    sourcePrefixCorridorSeparated_of_flatComponentCases_of_referenceFinalSegment_not_axisAligned
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
      fallbackRouteMember directRouteMember
      fallbackLength directLength directLast directTerminal
      fallbackRetained directRetained directClassified directFinalOblique
  · intro fallbackCarrier directMacrocell rectanglesNotSeparated
    exact
      sourcePrefixCorridorSeparated_of_flatCarrierMacrocell_rectangles_not_separated
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty
        fallbackRouteMember directRouteMember
        fallbackLength directLength routeIndicesDifferent headsDifferent
        fallbackHead directLast fallbackSourceNeDirectTarget
        directTerminal directClassified
        fallbackCarrier directMacrocell directFinalOblique
        rectanglesNotSeparated
  · intro fallbackMacrocell directMacrocell centersEqual
    have fallbackTaggedIncidenceMember :
        ((⟨fallbackClauseIndex, fallbackClause.literals,
            fallbackLiteralIndex, fallbackLiteral⟩ :
              CNFIncidence
                (WrappedPeriodicPlanarSATVariable Variable)),
          fallbackRouteIndex) ∈
            (finalGaugedIncidences formula).zipIdx := by
      simpa [finalGaugedIncidences, source,
        finalCoordinatedSource] using
        fallbackIncidenceMember
    exfalso
    exact
      FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_incidence_choice_none_of_second_finalSegment_not_axisAligned
        formula
        certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal
        fallbackMacrocell directMacrocell
        fallbackTaggedIncidenceMember fallbackChoiceNone
        directLength directLast directFinalOblique centersEqual

end PeriodicOrthocrossing
end LeanTrominoes

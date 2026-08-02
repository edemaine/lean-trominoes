import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup
import LeanTrominoes.RetainedFinalEscapedSourceScaledSpliceSeparation
import LeanTrominoes.RetainedFinalOuterFanSeparation
import LeanTrominoes.RetainedFinalSharedCenterFanSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATRasterizedDrawing
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularBoundaryRoutes

/-!
# Positioned-incidence interface for shared-center splice separation

The geometric shared-center theorem is phrased using flat route-list
memberships and indices.  Global route assembly instead starts with genuine
positioned clause and literal memberships.  This file derives all flat
lookup, length, and endpoint facts automatically and exposes the separator
at that positioned-incidence interface.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree
open PeriodicEightOccurrenceSplitPositioned
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Two distinct positioned source incidences of one retained variable,
ending at the same physical variable center but starting at different clause
centers, produce strictly separated source-scaled boundary splices. -/
theorem
    retainedFinalPositionedOccurrenceSplices_strictlyAvoid_of_sameCenter
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (fits :
      FitsEightSlots
        (PeriodicOrthocrossing.retainedDrawingAngularOccurrenceOrder
          formula))
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    {firstClause secondClause :
      PositionedPeriodicClause
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (atomsEqual : firstLiteral.atom = secondLiteral.atom)
    (copiesDifferent :
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex) ≠
        (secondLiteral.atom, secondClauseIndex, secondLiteralIndex))
    (sourcesDifferent :
      PositionedPeriodicCNF.canonicalClausePosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          firstClause ≠
        PositionedPeriodicCNF.canonicalClausePosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          secondClause)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          secondClause secondLiteral) :
    let routes :=
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula
    let firstCopy :
        ThreeOccurrenceVariable
          (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
    let secondCopy :
        ThreeOccurrenceVariable
          (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
      (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
    let firstCopyMember :
        firstCopy ∈
          occurrenceVariables
            (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
            firstLiteral.atom :=
      occurrenceVariables_mem
        (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
        (taggedLiteral_mem_of_positioned_members
          (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          firstClauseMember firstLiteralMember)
    let secondCopyMember :
        secondCopy ∈
          occurrenceVariables
            (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
            firstLiteral.atom :=
      atomsEqual ▸
        occurrenceVariables_mem
          (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
          (taggedLiteral_mem_of_positioned_members
            (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula)
            secondClauseMember secondLiteralMember)
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor
          (routes firstClauseIndex firstLiteralIndex))
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes firstCopy)))
        (retainedFinalAngularTerminalSlot
          formula fits firstLiteral.atom firstCopy firstCopyMember))
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor
          (routes secondClauseIndex secondLiteralIndex))
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes secondCopy)))
        (retainedFinalAngularTerminalSlot
          formula fits firstLiteral.atom secondCopy secondCopyMember)) := by
  let source :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula
  let routes :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  let firstCopy :
      ThreeOccurrenceVariable
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
  let secondCopy :
      ThreeOccurrenceVariable
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
    (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
  have firstCopyMember :
      firstCopy ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    exact occurrenceVariables_mem source.erase
      (taggedLiteral_mem_of_positioned_members
        source firstClauseMember firstLiteralMember)
  have secondCopyMember :
      secondCopy ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    have member :
        secondCopy ∈
          occurrenceVariables source.erase secondLiteral.atom := by
      exact occurrenceVariables_mem source.erase
        (taggedLiteral_mem_of_positioned_members
          source secondClauseMember secondLiteralMember)
    simpa [atomsEqual] using member
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        firstClauseMember firstLiteralMember with
    ⟨firstRouteIndex, firstIncidenceMember, firstRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        secondClauseMember secondLiteralMember with
    ⟨secondRouteIndex, secondIncidenceMember, secondRouteMember⟩
  have routeIndicesDifferent :
      firstRouteIndex ≠ secondRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      PeriodicOrthocrossing.tagged_eq_of_mem_zipIdx_of_snd_eq
        firstIncidenceMember secondIncidenceMember
        indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    simpa [firstCopy, secondCopy] using
      congrArg
        (fun incidence :
            CNFIncidence
              (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable
                Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual
  have firstLength :
      2 ≤ (routes firstClauseIndex firstLiteralIndex).length := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        firstClauseMember firstLiteralMember
  have secondLength :
      2 ≤ (routes secondClauseIndex secondLiteralIndex).length := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        secondClauseMember secondLiteralMember
  have firstEndpoints :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula wellFormed degree isLocal
      firstClauseMember firstLiteralMember
  have secondEndpoints :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula wellFormed degree isLocal
      secondClauseMember secondLiteralMember
  have compatible :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula wellFormed degree isLocal clausesNonempty
  have firstHeadNeLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @PeriodicOrthocrossing.instDecidableEqWrappedPeriodicVariable
          (PeriodicOrthocrossing.PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @PeriodicOrthocrossing.instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecidableEq
              firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _
      firstIncidenceMember firstIncidenceMember
  have secondHeadNeLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @PeriodicOrthocrossing.instDecidableEqWrappedPeriodicVariable
          (PeriodicOrthocrossing.PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @PeriodicOrthocrossing.instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecidableEq
              firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _
      secondIncidenceMember secondIncidenceMember
  have firstSourceNeCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral := by
    rw [firstEndpoints.1, firstEndpoints.2] at firstHeadNeLast
    simpa using firstHeadNeLast
  have secondSourceNeCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          placement secondClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement secondClause secondLiteral := by
    rw [secondEndpoints.1, secondEndpoints.2] at secondHeadNeLast
    simpa using secondHeadNeLast
  have headsDifferent :
      (routes firstClauseIndex firstLiteralIndex).head? ≠
        (routes secondClauseIndex secondLiteralIndex).head? := by
    rw [firstEndpoints.1, secondEndpoints.1]
    exact fun equal =>
      sourcesDifferent (Option.some.inj equal)
  have secondLast :
      (routes secondClauseIndex secondLiteralIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral) := by
    rw [secondEndpoints.2, centersEqual]
  simpa only [source, placement, routes, firstCopy, secondCopy] using
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_sameCenterOccurrences
      formula wellFormed degree isLocal clausesNonempty fits
      factorGreaterThanOne clearance
      firstLiteral.atom firstCopy secondCopy
      (by
        simpa [source,
          PeriodicOrthocrossing.retainedPlanarSATFormula] using
          firstCopyMember)
      (by
        simpa [source,
          PeriodicOrthocrossing.retainedPlanarSATFormula] using
          secondCopyMember)
      copiesDifferent
      rfl rfl
      firstRouteMember secondRouteMember
      firstLength secondLength routeIndicesDifferent headsDifferent
      firstEndpoints.1 secondEndpoints.1
      firstEndpoints.2 secondLast
      firstSourceNeCenter
      (by
        intro equal
        exact secondSourceNeCenter
          (equal.trans centersEqual))

/-- Two distinct positioned source incidences with different source and
variable endpoints produce strictly separated source-scaled boundary
splices whenever both discarded terminal segments are axis-aligned.  In
addition to ordinary/ordinary separation, the certificate supplies
escaped/ordinary and escaped/escaped separation whenever the corresponding
outer radial routes have room for the fixed delayed-lane escape.  Flat route
indices, endpoint equations, cross-endpoint inequalities, and terminal
classification are all derived from the positioned drawing certificates. -/
theorem
    retainedFinalPositionedOccurrenceSplices_strictlyAvoid_of_distinctCenters_of_axisAligned
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (fits :
      FitsEightSlots
        (PeriodicOrthocrossing.retainedDrawingAngularOccurrenceOrder
          formula))
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    {firstClause secondClause :
      PositionedPeriodicClause
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (copiesDifferent :
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex) ≠
        (secondLiteral.atom, secondClauseIndex, secondLiteralIndex))
    (sourcesDifferent :
      PositionedPeriodicCNF.canonicalClausePosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          firstClause ≠
        PositionedPeriodicCNF.canonicalClausePosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          secondClause)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          firstClause firstLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          secondClause secondLiteral)
    (firstAligned :
      (⟨polylineLastEntrance
          (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula firstClauseIndex firstLiteralIndex),
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula firstClauseIndex firstLiteralIndex).getLastD
            (0, 0)⟩ : GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨polylineLastEntrance
          (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula secondClauseIndex secondLiteralIndex),
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula secondClauseIndex secondLiteralIndex).getLastD
            (0, 0)⟩ : GridSegment).IsAxisAligned) :
    let routes :=
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula
    let firstCopy :
        ThreeOccurrenceVariable
          (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
    let secondCopy :
        ThreeOccurrenceVariable
          (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
      (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
    let firstCopyMember :
        firstCopy ∈
          occurrenceVariables
            (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
            firstLiteral.atom :=
      occurrenceVariables_mem
        (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
        (taggedLiteral_mem_of_positioned_members
          (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          firstClauseMember firstLiteralMember)
    let secondCopyMember :
        secondCopy ∈
          occurrenceVariables
            (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
            secondLiteral.atom :=
      occurrenceVariables_mem
        (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
        (taggedLiteral_mem_of_positioned_members
          (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          secondClauseMember secondLiteralMember)
    let firstTerminal :=
      classifiedRetainedTerminalData
        (occurrenceTerminalVector routes firstCopy)
    let secondTerminal :=
      classifiedRetainedTerminalData
        (occurrenceTerminalVector routes secondCopy)
    let firstSlot :=
      retainedFinalAngularTerminalSlot
        formula fits firstLiteral.atom firstCopy firstCopyMember
    let secondSlot :=
      retainedFinalAngularTerminalSlot
        formula fits secondLiteral.atom secondCopy secondCopyMember
    let firstOrdinary :=
      retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor
          (routes firstClauseIndex firstLiteralIndex))
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot
    let secondOrdinary :=
      retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor
          (routes secondClauseIndex secondLiteralIndex))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot
    let firstEscaped :=
      retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline factor
          (routes firstClauseIndex firstLiteralIndex))
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot
    let secondEscaped :=
      retainedAngularFanEscapedSplicedBoundaryPolyline
        (scalePolyline factor
          (routes secondClauseIndex secondLiteralIndex))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot
    RoutesStrictlyAvoidEachOther firstOrdinary secondOrdinary ∧
      (retainedTerminalFanOuterSourceEscapeLength ≤
          retainedTerminalFanOuterRadialLength
            (scaleRetainedTerminalData factor firstTerminal) →
        RoutesStrictlyAvoidEachOther firstEscaped secondOrdinary) ∧
      (retainedTerminalFanOuterSourceEscapeLength ≤
          retainedTerminalFanOuterRadialLength
            (scaleRetainedTerminalData factor firstTerminal) →
        retainedTerminalFanOuterSourceEscapeLength ≤
          retainedTerminalFanOuterRadialLength
            (scaleRetainedTerminalData factor secondTerminal) →
        RoutesStrictlyAvoidEachOther firstEscaped secondEscaped) := by
  let source :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula
  let routes :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  let firstCopy :
      ThreeOccurrenceVariable
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
  let secondCopy :
      ThreeOccurrenceVariable
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable) :=
    (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
  have firstCopyMember :
      firstCopy ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    exact occurrenceVariables_mem source.erase
      (taggedLiteral_mem_of_positioned_members
        source firstClauseMember firstLiteralMember)
  have secondCopyMember :
      secondCopy ∈
        occurrenceVariables source.erase secondLiteral.atom := by
    exact occurrenceVariables_mem source.erase
      (taggedLiteral_mem_of_positioned_members
        source secondClauseMember secondLiteralMember)
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        firstClauseMember firstLiteralMember with
    ⟨firstRouteIndex, firstIncidenceMember, firstRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        secondClauseMember secondLiteralMember with
    ⟨secondRouteIndex, secondIncidenceMember, secondRouteMember⟩
  have routeIndicesDifferent :
      firstRouteIndex ≠ secondRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      PeriodicOrthocrossing.tagged_eq_of_mem_zipIdx_of_snd_eq
        firstIncidenceMember secondIncidenceMember
        indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    simpa [firstCopy, secondCopy] using
      congrArg
        (fun incidence :
            CNFIncidence
              (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable
                Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual
  have firstLength :
      2 ≤ (routes firstClauseIndex firstLiteralIndex).length := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        firstClauseMember firstLiteralMember
  have secondLength :
      2 ≤ (routes secondClauseIndex secondLiteralIndex).length := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        secondClauseMember secondLiteralMember
  have firstEndpoints :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula wellFormed degree isLocal
      firstClauseMember firstLiteralMember
  have secondEndpoints :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula wellFormed degree isLocal
      secondClauseMember secondLiteralMember
  have compatible :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula wellFormed degree isLocal clausesNonempty
  have firstHeadNeSecondLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @PeriodicOrthocrossing.instDecidableEqWrappedPeriodicVariable
          (PeriodicOrthocrossing.PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @PeriodicOrthocrossing.instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecidableEq
              firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _
      firstIncidenceMember secondIncidenceMember
  have secondHeadNeFirstLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @PeriodicOrthocrossing.instDecidableEqWrappedPeriodicVariable
          (PeriodicOrthocrossing.PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @PeriodicOrthocrossing.instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecidableEq
              firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _
      secondIncidenceMember firstIncidenceMember
  have headsDifferent :
      (routes firstClauseIndex firstLiteralIndex).head? ≠
        (routes secondClauseIndex secondLiteralIndex).head? := by
    rw [firstEndpoints.1, secondEndpoints.1]
    exact fun equal =>
      sourcesDifferent (Option.some.inj equal)
  have firstSourceNeSecondCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement secondClause secondLiteral := by
    rw [firstEndpoints.1, secondEndpoints.2] at firstHeadNeSecondLast
    simpa using firstHeadNeSecondLast
  have secondSourceNeFirstCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          placement secondClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral := by
    rw [secondEndpoints.1, firstEndpoints.2] at secondHeadNeFirstLast
    simpa using secondHeadNeFirstLast
  let firstTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes firstCopy)
  let secondTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes secondCopy)
  let firstSlot :=
    retainedFinalAngularTerminalSlot
      formula fits firstLiteral.atom firstCopy
        (by
          simpa [source,
            PeriodicOrthocrossing.retainedPlanarSATFormula] using
            firstCopyMember)
  let secondSlot :=
    retainedFinalAngularTerminalSlot
      formula fits secondLiteral.atom secondCopy
        (by
          simpa [source,
            PeriodicOrthocrossing.retainedPlanarSATFormula] using
            secondCopyMember)
  have retained :
      RetainedOccurrenceTerminalCertificate
        (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
        routes := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        formula wellFormed degree isLocal clausesNonempty
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (routes firstClauseIndex firstLiteralIndex)) =
        some firstTerminal := by
    exact
      retainedTerminalDirectionClassify_classifiedRetainedTerminalData
        (retained firstLiteral.atom firstCopy
          (by
            simpa [source,
              PeriodicOrthocrossing.retainedPlanarSATFormula] using
              firstCopyMember))
  have secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (routes secondClauseIndex secondLiteralIndex)) =
        some secondTerminal := by
    exact
      retainedTerminalDirectionClassify_classifiedRetainedTerminalData
        (retained secondLiteral.atom secondCopy
          (by
            simpa [source,
              PeriodicOrthocrossing.retainedPlanarSATFormula] using
              secondCopyMember))
  constructor
  · simpa only [source, placement, routes, firstCopy, secondCopy,
      firstTerminal, secondTerminal, firstSlot, secondSlot] using
      retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_distinctEndpoints_of_axisAligned
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne clearance
        firstRouteMember secondRouteMember
        firstLength secondLength routeIndicesDifferent headsDifferent
        firstEndpoints.1 secondEndpoints.1
        firstEndpoints.2 secondEndpoints.2
        firstSourceNeSecondCenter secondSourceNeFirstCenter
        centersDifferent firstAligned secondAligned
        firstTerminal secondTerminal firstSlot secondSlot
        firstClassified secondClassified
  constructor
  · intro firstEscapeFits
    simpa only [source, placement, routes, firstCopy, secondCopy,
      firstTerminal, secondTerminal, firstSlot, secondSlot] using
      retainedFinalSourceScaledEscapedOrdinarySplicedBoundaryPolylines_strictlyAvoid_of_distinctEndpoints_of_axisAligned
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne
        (by omega)
        firstRouteMember secondRouteMember
        firstLength secondLength routeIndicesDifferent headsDifferent
        firstEndpoints.1 secondEndpoints.1
        firstEndpoints.2 secondEndpoints.2
        firstSourceNeSecondCenter secondSourceNeFirstCenter
        centersDifferent firstAligned secondAligned
        firstTerminal secondTerminal firstSlot secondSlot
        firstClassified secondClassified firstEscapeFits
  · intro firstEscapeFits secondEscapeFits
    simpa only [source, placement, routes, firstCopy, secondCopy,
      firstTerminal, secondTerminal, firstSlot, secondSlot] using
      retainedFinalSourceScaledEscapedSplicedBoundaryPolylines_strictlyAvoid_of_distinctEndpoints_of_axisAligned
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne
        (by omega)
        firstRouteMember secondRouteMember
        firstLength secondLength routeIndicesDifferent headsDifferent
        firstEndpoints.1 secondEndpoints.1
        firstEndpoints.2 secondEndpoints.2
        firstSourceNeSecondCenter secondSourceNeFirstCenter
        centersDifferent firstAligned secondAligned
        firstTerminal secondTerminal firstSlot secondSlot
        firstClassified secondClassified firstEscapeFits secondEscapeFits

end PeriodicEightOccurrenceSplit
end LeanTrominoes

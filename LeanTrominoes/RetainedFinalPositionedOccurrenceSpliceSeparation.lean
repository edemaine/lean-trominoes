import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup
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
          secondClause secondLiteral)
    (firstSourceNeCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          firstClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          firstClause firstLiteral)
    (secondSourceNeCenter :
      PositionedPeriodicCNF.canonicalClausePosition
          (PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula)
          secondClause ≠
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

end PeriodicEightOccurrenceSplit
end LeanTrominoes

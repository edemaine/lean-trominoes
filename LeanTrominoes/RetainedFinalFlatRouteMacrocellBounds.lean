/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteMacrocellBounds

/-!
# Macrocell bounds from flat final route membership

Downstream angular-fan proofs see the final periodic drawing only through a
flat `(route, routeIndex)` membership.  This file packages the metadata
coordinates and physical occurrence recovered from that membership, at the
untranslated occurrence used by `edgeRoutes`.

For noncarrier routes the package also records the unique advertised
macrocell center.  Two such packages with different translated centers
therefore provide the source-prefix/complete-route rectangle certificate
required by the retained-terminal rasterization bridge.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Clause/literal coordinates and their physical retained representative
for one route in the flat final `edgeRoutes` list. -/
structure FinalGaugedFlatRouteOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedRoute : List Cell × Nat) where
  coordinates :
    FinalGaugedRouteCoordinates formula taggedRoute
  routeWitness :
    FinalGaugedRouteOccurrenceWitness
      formula coordinates.taggedClause.2
        coordinates.taggedLiteral.2 (0, 0)

/-- Every flat final route membership recovers a physical retained route
occurrence without requiring a segment or point index. -/
theorem exists_finalGaugedFlatRouteOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (taggedRoute : List Cell × Nat)
    (taggedRouteMember :
      taggedRoute ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx) :
    Nonempty
      (FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute) := by
  rcases exists_finalGaugedRouteCoordinates
      formula taggedRoute taggedRouteMember with
    ⟨coordinates⟩
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula wellFormed degree isLocal clausesNonempty
        coordinates.taggedClause
        coordinates.taggedClauseMember
        coordinates.taggedLiteral
        coordinates.taggedLiteralMember
        (0, 0) with
    ⟨routeWitness⟩
  exact ⟨⟨coordinates, routeWitness⟩⟩

/-- At period shift zero, the route occurrence stored by the flat witness is
definitionally the listed final route after simplifying zero translation. -/
theorem FinalGaugedFlatRouteOccurrenceWitness.finalRoute_eq_occurrence
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute) :
    taggedRoute.1 =
      finalGaugedRouteOccurrence
        formula witness.coordinates.taggedClause.2
          witness.coordinates.taggedLiteral.2 (0, 0) := by
  unfold finalGaugedRouteOccurrence
  have zeroTranslation :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation (0, 0) = (0, 0) := by
    simp [PeriodicVariablePlacement.translation, Cell.scale]
  rw [zeroTranslation]
  have translatePolyline_zero (points : List Cell) :
      translatePolyline (0, 0) points = points := by
    induction points with
    | nil => rfl
    | cons point points induction =>
        change
          List.map (Cell.add (0, 0)) points = points at induction
        simp only [translatePolyline, List.map_cons]
        rw [induction]
        simp [Cell.add]
  rw [translatePolyline_zero]
  exact witness.coordinates.finalRouteEq

/-- A flat route witness whose physical component is noncarrier, packaged
with its advertised macrocell center. -/
structure FinalGaugedFlatRouteMacrocellWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedRoute : List Cell × Nat)
    extends FinalGaugedFlatRouteOccurrenceWitness formula taggedRoute where
  center : Cell
  centerEq :
    toFinalGaugedFlatRouteOccurrenceWitness.routeWitness.metadata.source.component.macrocellCenter
        formula =
      some center

/-- A recovered flat occurrence has a macrocell package whenever its
physical component is not a carrier lens. -/
theorem
    FinalGaugedFlatRouteOccurrenceWitness.exists_macrocellWitness_of_not_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute)
    (notCarrier :
      ¬∃ link,
        witness.routeWitness.metadata.source.component =
          .carrier link) :
    Nonempty
      (FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) := by
  rcases
      witness.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula notCarrier with
    ⟨center, centerEq⟩
  exact ⟨{
    toFinalGaugedFlatRouteOccurrenceWitness := witness
    center := center
    centerEq := centerEq
  }⟩

/-- The translated physical component center of a flat final route. -/
def FinalGaugedFlatRouteMacrocellWitness.translatedCenter
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute) :
    Cell :=
  witness.routeWitness.translatedMacrocellCenter witness.center

/-- Every point of a macrocell-packaged flat route lies in the rectangle at
its translated physical component center. -/
theorem
    FinalGaugedFlatRouteMacrocellWitness.routePoints_in_translatedMacrocell
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute)
    {point : Cell}
    (pointMember : point ∈ taggedRoute.1) :
    InPlanarSATMacrocell witness.translatedCenter point := by
  rw [witness.finalRoute_eq_occurrence] at pointMember
  exact
    witness.routeWitness.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal
      witness.center witness.centerEq pointMember

/-- Distinct translated macrocells of two flat final routes give the exact
rectangle certificate for the first route's retained source prefix against
the second complete route. -/
theorem
    sourcePrefixPolylineRectanglesSeparated_of_flatRouteMacrocellCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstTaggedRoute secondTaggedRoute : List Cell × Nat}
    (first :
      FinalGaugedFlatRouteMacrocellWitness
        formula firstTaggedRoute)
    (second :
      FinalGaugedFlatRouteMacrocellWitness
        formula secondTaggedRoute)
    (centersDifferent :
      first.translatedCenter ≠ second.translatedCenter) :
    PeriodicEightOccurrenceSplit.SourcePolylineRectanglesSeparated
      firstTaggedRoute.1.dropLast secondTaggedRoute.1 := by
  apply
    PeriodicEightOccurrenceSplit.SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
      (firstLower :=
        planarSATMacrocellRouteLower first.translatedCenter)
      (firstUpper :=
        planarSATMacrocellRouteUpper first.translatedCenter)
      (secondLower :=
        planarSATMacrocellRouteLower second.translatedCenter)
      (secondUpper :=
        planarSATMacrocellRouteUpper second.translatedCenter)
  · intro point pointMember
    exact first.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal
      (List.mem_of_mem_dropLast pointMember)
  · intro point pointMember
    exact second.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal pointMember
  · exact planarSATMacrocellRouteRectangles_separated centersDifferent

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The distinct-noncarrier-macrocell case of the directed retained
source-prefix/fan separation theorem, stated directly for flat final routes.
All physical occurrence and rectangle certificates are recovered by the two
macrocell witnesses. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_flatRouteMacrocellCenters_ne
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
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    {sourceRoute referenceRoute : List Cell}
    {sourceIndex referenceIndex : Nat}
    {sourcePoint referenceCenter : Cell}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (referenceMember :
      (referenceRoute, referenceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (indicesDifferent : sourceIndex ≠ referenceIndex)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (referenceLast :
      referenceRoute.getLast? = some referenceCenter)
    (sourceNeCenter : sourcePoint ≠ referenceCenter)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourceMacrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula (sourceRoute, sourceIndex))
    (referenceMacrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula (referenceRoute, referenceIndex))
    (centersDifferent :
      sourceMacrocell.translatedCenter ≠
        referenceMacrocell.translatedCenter) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor referenceCenter))
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot) := by
  apply
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_sourcePolylineRectanglesSeparated
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      sourceMember referenceMember sourceLength referenceLength
      indicesDifferent sourceHead referenceLast sourceNeCenter
      referenceTerminal referenceSlot referenceClassified
  exact
    PeriodicOrthocrossing.sourcePrefixPolylineRectanglesSeparated_of_flatRouteMacrocellCenters_ne
      formula wellFormed degree isLocal
      sourceMacrocell referenceMacrocell centersDifferent

end PeriodicEightOccurrenceSplit
end LeanTrominoes

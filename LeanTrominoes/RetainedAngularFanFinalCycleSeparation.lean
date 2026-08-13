/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleMacrocellSeparation
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-!
# Implication-cycle separation in the final coordinated fixed-eight family

The generic Figure 7 macrocell theorem assumes that source positions are
injective on variables that occur.  The final retained planar-SAT placement
already has exactly that property for geometrically valid variables.  This
file discharges the generic premise from the retained source certificate and
then transports the resulting cycle-route separation through the source
clearance and terminal-fan refinements used by the final coordinated family.
-/

namespace LeanTrominoes

/-- Positive uniform scaling preserves the complete finite route-simplicity
predicate. -/
theorem routeIsSimple_scalePolyline
    {route : List Cell}
    {factor : Int} (factorPositive : 0 < factor)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline factor route) := by
  let geometry :
      PlanarThreeSAT.GridDrawingMap (Cell.scale factor) :=
    { injective := Cell.scale_injective factorPositive.ne'
      isAxisAligned := fun {segment} aligned => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          (GridSegment.isAxisAligned_scale_iff
            factorPositive segment).mpr aligned
      interiorContains_iff := fun {segment point} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorContains_scale_iff
            factorPositive segment point
      interiorsMeet_iff := fun {first second} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorsMeet_scale_iff
            factorPositive first second }
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_mapPoints
      geometry simple

namespace PeriodicThreeSATThree

/-- Every atom in the duplicate-free source-variable list is a literal
occurrence of the source formula. -/
theorem sourceVariables_subset_variableOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ∀ ⦃atom⦄,
      atom ∈ sourceVariables source →
        atom ∈ source.variableOccurrences := by
  intro atom atomMember
  rw [sourceVariables, List.mem_dedup,
    List.mem_map] at atomMember
  rcases atomMember with
    ⟨taggedLiteral, taggedLiteralMember, atomEqual⟩
  rw [taggedLiterals, List.mem_flatMap]
    at taggedLiteralMember
  rcases taggedLiteralMember with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteralMember⟩
  rcases List.mem_map.mp taggedLiteralMember with
    ⟨taggedClauseLiteral, taggedClauseLiteralMember,
      taggedLiteralEqual⟩
  unfold PeriodicCNF.variableOccurrences
  apply List.mem_flatMap.mpr
  refine
    ⟨taggedClause.1,
      List.fst_mem_of_mem_zipIdx taggedClauseMember, ?_⟩
  apply List.mem_map.mpr
  refine
    ⟨taggedClauseLiteral.1,
      List.fst_mem_of_mem_zipIdx taggedClauseLiteralMember, ?_⟩
  rw [← atomEqual]
  exact congrArg (fun tagged => tagged.1.atom)
    taggedLiteralEqual

end PeriodicThreeSATThree

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Source-clearance scaling preserves injectivity of the final gauged
placement on variables that actually occur in the retained source. -/
theorem
    retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    ∀ {firstAtom secondAtom :
        WrappedPeriodicPlanarSATVariable Variable},
      firstAtom ∈ sourceVariables source.erase →
        secondAtom ∈ sourceVariables source.erase →
          placement.position firstAtom =
              placement.position secondAtom →
            firstAtom = secondAtom := by
  dsimp only
  intro firstAtom secondAtom
    firstAtomMember secondAtomMember positionsEqual
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have firstOccurrence :
      firstAtom ∈
        (finalCoordinatedSource formula).erase.variableOccurrences := by
    apply sourceVariables_subset_variableOccurrences
    simpa only [PositionedPeriodicCNF.erase_scale]
      using firstAtomMember
  have secondOccurrence :
      secondAtom ∈
        (finalCoordinatedSource formula).erase.variableOccurrences := by
    apply sourceVariables_subset_variableOccurrences
    simpa only [PositionedPeriodicCNF.erase_scale]
      using secondAtomMember
  have firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula firstAtom.original := by
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        (by simpa [finalCoordinatedSource] using firstOccurrence)
  have secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula secondAtom.original := by
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        (by simpa [finalCoordinatedSource] using secondOccurrence)
  apply
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      firstValid secondValid
  apply Cell.scale_injective
    (show
      (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
      simp [retainedAngularFanSourceClearanceFactor])
  simpa [finalCoordinatedPlacement] using positionsEqual

/-- At an appended implication-clause index, the public coordinated family
is definitionally the unchanged factor-eight Figure 7 route. -/
theorem retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (cycleIndex literalIndex : Nat) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes)
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula
        ((occurrenceClauses source occurrencePorts).length +
          cycleIndex)
        literalIndex =
      scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes source placement
          cycleIndex literalIndex) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let occurrencePorts :=
    occurrencePortsOfAngularOrder
      source.erase
      (angularOccurrenceOrder source.erase routes)
  have clauseNone :
      finalCoordinatedScaledClause? formula
          ((occurrenceClauses source occurrencePorts).length +
            cycleIndex) =
        none := by
    apply List.getElem?_eq_none_iff.mpr
    simp [source, finalCoordinatedSource,
      PeriodicEightOccurrenceSplitPositioned.occurrenceClauses]
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_clause_none
      formula
      ((occurrenceClauses source occurrencePorts).length +
        cycleIndex)
      literalIndex clauseNone]
  exact
    retainedAngularFanSplicedIncidenceRoutes_cycle
      source
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      routes cycleIndex literalIndex

/-- Every factor-eight implication route used by the retained construction
remains simple. -/
theorem retainedFinalSourceScaledAllCycleRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex literalIndex)) := by
  apply routeIsSimple_scalePolyline
    (show (0 : Int) < retainedTerminalFanRoutingRefinement by
      simp [retainedTerminalFanRoutingRefinement])
  exact
    allCycleRoute_isSimple
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      clauseMember literalMember

/-- Route simplicity in the public coordinated interface at an appended
implication-clause index. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes)
    LocalIncidenceDrawing.RouteIsSimple
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula
        ((occurrenceClauses source occurrencePorts).length +
          cycleIndex)
        literalIndex) := by
  dsimp only
  rw [
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula cycleIndex literalIndex]
  exact
    retainedFinalSourceScaledAllCycleRoute_isSimple
      formula clauseMember literalMember

/-- The final factor-eight placement of a Figure 7 ring-copy vertex avoids
every segment of every factor-eight implication route. -/
theorem retainedFinalSourceScaledAllCycleRingVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {vertexAtom : WrappedPeriodicPlanarSATVariable Variable}
    (vertexAtomMember :
      vertexAtom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase)
    (vertex : OccurrenceSplitRing.RingVertex)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex literalIndex))) :
    ¬segment.InteriorContains
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).position
          (ringCopy vertexAtom vertex)) := by
  rw [gridPolylineSegments_scalePolyline] at segmentMember
  rcases List.mem_map.mp segmentMember with
    ⟨sourceSegment, sourceSegmentMember, rfl⟩
  have avoids :=
    allCycleRingVertex_avoidsRouteInterior
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      (retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      vertexAtomMember vertex
      clauseMember literalMember sourceSegmentMember
  simpa [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,
    retainedAngularFanRefinedPlacement,
    finalCoordinatedPlacement] using
      (mt
        (GridSegment.interiorContains_scale_iff
          (show
            (0 : Int) < retainedTerminalFanRoutingRefinement by
            simp [retainedTerminalFanRoutingRefinement])
          sourceSegment
          (((PeriodicEightOccurrenceSplitPositioned.placement
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)).position
              (ringCopy vertexAtom vertex)))).mp
        avoids)

/-- Vertex/interior avoidance for a Figure 7 ring-copy vertex in the public
coordinated route-family interface at an appended implication-clause
index. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleRingVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {vertexAtom : WrappedPeriodicPlanarSATVariable Variable}
    (vertexAtomMember :
      vertexAtom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase)
    (vertex : OccurrenceSplitRing.RingVertex)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      let source :=
        (finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor
      let routes :=
        PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes formula)
      let occurrencePorts :=
        occurrencePortsOfAngularOrder
          source.erase
          (angularOccurrenceOrder source.erase routes)
      segment ∈ gridPolylineSegments
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length +
            cycleIndex)
          literalIndex)) :
    ¬segment.InteriorContains
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).position
          (ringCopy vertexAtom vertex)) := by
  dsimp only at segmentMember
  rw [
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula cycleIndex literalIndex] at segmentMember
  exact
    retainedFinalSourceScaledAllCycleRingVertex_avoidsRouteInterior
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty vertexAtomMember vertex
      clauseMember literalMember segmentMember

/-- Every factor-eight implication-clause vertex avoids every segment of
every factor-eight implication route. -/
theorem retainedFinalSourceScaledAllCycleClauseVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {vertexClause routeClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {vertexCycleIndex routeCycleIndex : Nat}
    (vertexClauseMember :
      (vertexClause, vertexCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (routeClauseMember :
      (routeClause, routeCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ routeClause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            routeCycleIndex literalIndex))) :
    ¬segment.InteriorContains
      (Cell.scale retainedTerminalFanRoutingRefinement
        vertexClause.position) := by
  rw [gridPolylineSegments_scalePolyline] at segmentMember
  rcases List.mem_map.mp segmentMember with
    ⟨sourceSegment, sourceSegmentMember, rfl⟩
  have avoids :=
    allCycleClauseVertex_avoidsRouteInterior
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      (retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      vertexClauseMember routeClauseMember
      literalMember sourceSegmentMember
  exact
    mt
      (GridSegment.interiorContains_scale_iff
        (show
          (0 : Int) < retainedTerminalFanRoutingRefinement by
          simp [retainedTerminalFanRoutingRefinement])
        sourceSegment vertexClause.position).mp
      avoids

/-- Cycle-clause-vertex/interior avoidance in the public coordinated route
family at an appended implication-clause index. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleClauseVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {vertexClause routeClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {vertexCycleIndex routeCycleIndex : Nat}
    (vertexClauseMember :
      (vertexClause, vertexCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (routeClauseMember :
      (routeClause, routeCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ routeClause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      let source :=
        (finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor
      let routes :=
        PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes formula)
      let occurrencePorts :=
        occurrencePortsOfAngularOrder
          source.erase
          (angularOccurrenceOrder source.erase routes)
      segment ∈ gridPolylineSegments
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length +
            routeCycleIndex)
          literalIndex)) :
    ¬segment.InteriorContains
      (Cell.scale retainedTerminalFanRoutingRefinement
        vertexClause.position) := by
  dsimp only at segmentMember
  rw [
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula routeCycleIndex literalIndex] at segmentMember
  exact
    retainedFinalSourceScaledAllCycleClauseVertex_avoidsRouteInterior
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty vertexClauseMember routeClauseMember
      literalMember segmentMember

/-- The actual factor-eight implication routes used by the final retained
fixed-eight construction are pairwise continuously separated. -/
theorem retainedFinalSourceScaledAllCycleRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (incidencesDistinct :
      firstCycleIndex ≠ secondCycleIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          firstCycleIndex firstLiteralIndex))
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          secondCycleIndex secondLiteralIndex)) := by
  apply RoutesAvoidEachOther.scalePolyline
    (show (0 : Int) < retainedTerminalFanRoutingRefinement by
      simp [retainedTerminalFanRoutingRefinement])
  apply allCycleRoutes_avoidEachOther
    ((finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor)
    ((finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor)
  · exact
      retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact firstClauseMember
  · exact secondClauseMember
  · exact firstLiteralMember
  · exact secondLiteralMember
  · exact incidencesDistinct

/-- Pairwise cycle-suffix separation in the public coordinated route-family
interface, at the actual appended clause indices of the final formula. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (incidencesDistinct :
      firstCycleIndex ≠ secondCycleIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes)
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula
        ((occurrenceClauses source occurrencePorts).length +
          firstCycleIndex)
        firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula
        ((occurrenceClauses source occurrencePorts).length +
          secondCycleIndex)
        secondLiteralIndex) := by
  dsimp only
  rw [
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula firstCycleIndex firstLiteralIndex,
    retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
      formula secondCycleIndex secondLiteralIndex]
  exact
    retainedFinalSourceScaledAllCycleRoutes_avoidEachOther
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      incidencesDistinct

end PeriodicOrthocrossing
end LeanTrominoes

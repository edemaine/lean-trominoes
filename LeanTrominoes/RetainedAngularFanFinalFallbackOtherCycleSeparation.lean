/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCycleBounds
import LeanTrominoes.RetainedAngularFanFinalFallbackOtherSourceNeighborhood

/-!
# Final fallback occurrences avoid cycles at other source centers

The flattened implication-cycle lookup carries metadata naming the one
source atom that owns the selected cycle block.  Keeping that metadata fixed
outside the point quantifier strengthens the existing radius-48 bound into a
reusable center certificate.  A fallback occurrence whose canonical endpoint
is a different source center then inherits strict separation from the whole
cycle route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- After the terminal-fan refinement, every point of a flattened
implication route lies in the radius-48 rectangle centered at the atom
recorded by its fixed metadata lookup. -/
theorem
    scaledAllCycleRoute_point_in_metadataCenterRectangle
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {metadata : CycleClauseMetadata Variable}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        source sourcePlacement)[cycleIndex]? =
        some metadata)
    (literalIndex : Nat)
    {point : Cell}
    (pointMember :
      point ∈
        scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            source sourcePlacement
            cycleIndex literalIndex)) :
    InClosedGridRectangle
      (coordinateRadiusLower 48
        (Cell.scale
          (retainedTerminalFanRoutingRefinement *
            refinementScale)
          (sourcePlacement.position metadata.atom)))
      (coordinateRadiusUpper 48
        (Cell.scale
          (retainedTerminalFanRoutingRefinement *
            refinementScale)
          (sourcePlacement.position metadata.atom)))
      point := by
  rw [scalePolyline, List.mem_map] at pointMember
  rcases pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localPointMember' :
      localPoint ∈
        positionedCycleRoutes sourcePlacement metadata.atom
          metadata.localClauseIndex literalIndex := by
    unfold allCycleRoutes at localPointMember
    rw [metadataLookup] at localPointMember
    exact localPointMember
  have localBound :=
    positionedCycleRoutes_inClosedGridRectangle
      sourcePlacement metadata.atom metadata.localClauseIndex
      literalIndex localPointMember'
  rcases positionEq :
      sourcePlacement.position metadata.atom with
    ⟨centerX, centerY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  simp only [positionedCycleRouteLower, positionedCycleRouteUpper,
    macroOrigin,
    coordinateRadiusLower, coordinateRadiusUpper,
    retainedTerminalFanRoutingRefinement,
    refinementScale, positionEq, InClosedGridRectangle,
    Cell.add, Cell.sub, Cell.scale]
    at localBound ⊢
  omega

/-- Every point of a flattened final implication route lies in the radius-48
rectangle centered at the atom recorded by its fixed metadata lookup. -/
theorem
    retainedFinalSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (literalIndex : Nat)
    {point : Cell}
    (pointMember :
      point ∈
        scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex literalIndex)) :
    InClosedGridRectangle
      (coordinateRadiusLower 48
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).position
            metadata.atom)))
      (coordinateRadiusUpper 48
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).position
            metadata.atom)))
      point := by
  have bounded :=
    scaledAllCycleRoute_point_in_metadataCenterRectangle
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadataLookup literalIndex pointMember
  simpa [PeriodicVariablePlacement.scale,
    retainedTerminalFanTotalRefinement_eq,
    retainedTerminalFanRoutingRefinement,
    retainedAngularFanSourceClearanceFactor,
    refinementScale, Cell.scale_scale,
    Nat.cast_mul] using bounded

/-- A failed-choice occurrence is strictly separated from a flattened
implication-cycle route whenever its canonical source endpoint differs from
the cycle metadata's owning source center. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_allCycleRoute_of_center_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        (finalCoordinatedPlacement formula).position
          metadata.atom) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          cycleIndex cycleLiteralIndex)) := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let cycleRoute :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (allCycleRoutes source placement
        cycleIndex cycleLiteralIndex)
  have targetAtomMemberScaled :
      metadata.atom ∈ sourceVariables source.erase := by
    exact
      allCycleClauseMetadata_lookup_atom_mem
        source placement metadataLookup
  have targetAtomMember :
      metadata.atom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase := by
    simpa only [source,
      PositionedPeriodicCNF.erase_scale] using
      targetAtomMemberScaled
  have cycleBounded :
      ∀ point ∈ cycleRoute,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).position
                metadata.atom)))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).position
                metadata.atom)))
          point := by
    intro point pointMember
    apply inClosedGridRectangle_coordinateRadius_mono
      (smaller := 48) (larger := 96)
    · simpa [source, placement, cycleRoute] using
        retainedFinalSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
          formula metadataLookup cycleLiteralIndex pointMember
    · omega
  simpa [source, placement, cycleRoute] using
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_otherSourceNeighborhood
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone
      metadata.atom targetAtomMember centersDifferent
      cycleRoute cycleBounded

end PeriodicOrthocrossing
end LeanTrominoes

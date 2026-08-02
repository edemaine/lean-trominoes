import LeanTrominoes.RetainedAngularFanDirectSourceCarrierBoundarySeparation
import LeanTrominoes.RetainedFinalFlatRouteComponentCases

/-!
# Final routed-clause source-prefix separation

The routed-clause escape is handled locally at an overlapping carrier
boundary.  This file supplies the complementary coarse geometry: a selected
direct replacement remains in the radius-288 expansion of its flat
macrocell, and separated component boxes remain separated after the common
factor-1152 refinement.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A represented direct replacement stays in the radius-288 expansion of
the complete flat macrocell containing its original two-point route. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_point_in_scaledMacrocellRectangle_of_routeEq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        taggedRoute.1)
    {point : Cell}
    (pointMember : point ∈ choice.completeRoute slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          (PeriodicOrthocrossing.planarSATMacrocellRouteLower
            macrocell.translatedCenter)))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
            macrocell.translatedCenter)))
      point := by
  have localLength :=
    retainedDirectSourceLocalRouteAt_length choice.kind choice.index
  rcases List.length_eq_two.mp localLength with
    ⟨localHead, localLast, localRouteEq⟩
  have sourceStartMember : choice.sourceSegment.start ∈ taggedRoute.1 := by
    rw [← choiceRouteEq]
    simp [localRouteEq, PeriodicOrthocrossing.translatePolyline,
      RetainedDirectSourceRouteChoice.sourceSegment]
  have sourceFinishMember : choice.sourceSegment.finish ∈ taggedRoute.1 := by
    rw [← choiceRouteEq]
    simp [localRouteEq, PeriodicOrthocrossing.translatePolyline,
      RetainedDirectSourceRouteChoice.sourceSegment]
  have startBound :=
    macrocell.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal sourceStartMember
  have finishBound :=
    macrocell.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal sourceFinishMember
  have choiceBound :=
    choice.completeRoute_point_in_sourceSegmentRectangle
      slot pointMember
  rcases choice.sourceSegment.start with ⟨startX, startY⟩
  rcases choice.sourceSegment.finish with ⟨finishX, finishY⟩
  rcases lowerEq : PeriodicOrthocrossing.planarSATMacrocellRouteLower
      macrocell.translatedCenter with ⟨lowerX, lowerY⟩
  rcases upperEq : PeriodicOrthocrossing.planarSATMacrocellRouteUpper
      macrocell.translatedCenter with ⟨upperX, upperY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [PeriodicOrthocrossing.InPlanarSATMacrocell,
    InClosedGridRectangle] at startBound finishBound
  simp only [lowerEq, upperEq] at startBound finishBound ⊢
  have factorPositive :
      (0 : Int) < retainedTerminalFanTotalRefinement * 4 := by
    native_decide
  simp only [GridSegment.coordinateLower,
    GridSegment.coordinateUpper, coordinateRadiusLower,
    coordinateRadiusUpper, Cell.scale,
    InClosedGridRectangle] at choiceBound ⊢
  norm_num [retainedTerminalFanTotalRefinement_eq]
    at choiceBound factorPositive ⊢
  omega

/-- Scaling two separated component boxes by the final factor and expanding
both by radius 288 strictly separates a bounded source prefix from a bounded
direct replacement. -/
theorem
    scaledFlatPrefix_strictlyAvoids_directCompleteRoute_of_componentRectanglesSeparated
    {sourceRoute : List Cell}
    {sourceLower sourceUpper directLower directUpper : Cell}
    (sourcePrefixBounded :
      ∀ point ∈ sourceRoute.dropLast,
        InClosedGridRectangle sourceLower sourceUpper point)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (directBounded :
      ∀ point ∈ choice.completeRoute slot,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              directLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              directUpper))
          point)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        sourceLower sourceUpper directLower directUpper) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (choice.completeRoute slot) := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
    (firstLower :=
      coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          sourceLower))
    (firstUpper :=
      coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          sourceUpper))
    (secondLower :=
      coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          directLower))
    (secondUpper :=
      coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          directUpper))
  · intro point pointMember
    unfold scalePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    have bounded :=
      sourcePrefixBounded sourcePoint sourcePointMember
    rcases sourceLower with ⟨lowerX, lowerY⟩
    rcases sourceUpper with ⟨upperX, upperY⟩
    rcases sourcePoint with ⟨sourceX, sourceY⟩
    simp only [InClosedGridRectangle] at bounded
    have factorPositive :
        (0 : Int) < retainedTerminalFanTotalRefinement * 4 := by
      native_decide
    simp only [coordinateRadiusLower, coordinateRadiusUpper,
      Cell.scale, InClosedGridRectangle]
    norm_num [retainedTerminalFanTotalRefinement_eq]
      at bounded factorPositive ⊢
    omega
  · exact directBounded
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        rectanglesSeparated
        (by native_decide) (by native_decide)

/-- Flat-component analysis reduces routed-clause source-prefix separation to
the equal-macrocell residue.  A direct carrier is impossible by obliqueness;
separated component boxes use the coarse bound above, and the sole
overlapping carrier--macrocell branch uses the specialized inward-boundary
escape together with the supplied post-escape tail certificate. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute_of_flatComponentCases
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {sourceRoute directRoute : List Cell}
    {sourceIndex directIndex : Nat}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (directMember :
      (directRoute, directIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (directLength : 2 ≤ directRoute.length)
    {directTarget : Cell}
    (directLast : directRoute.getLast? = some directTarget)
    (directOblique :
      ¬(⟨polylineLastEntrance directRoute, directTarget⟩ :
        GridSegment).IsAxisAligned)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (kindEq : choice.kind = RetainedDirectClauseKind.routedClause)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) = directRoute)
    (tailAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline
          (retainedTerminalFanTotalRefinement * 4)
          sourceRoute.dropLast)
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedDirectSourceFanCompleteTailAt
            choice.kind choice.index slot)))
    (equalMacrocells :
      ∀
        (sourceMacrocell :
          PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
            formula (sourceRoute, sourceIndex))
        (directMacrocell :
          PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
            formula (directRoute, directIndex)),
        sourceMacrocell.translatedCenter =
            directMacrocell.translatedCenter →
          RoutesStrictlyAvoidEachOther
            (scalePolyline
              (retainedTerminalFanTotalRefinement * 4)
              sourceRoute.dropLast)
            (choice.completeRoute slot)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (choice.completeRoute slot) := by
  rcases
      PeriodicOrthocrossing.exists_finalGaugedFlatCarrier_or_macrocellWitness
        formula wellFormed degree isLocal clausesNonempty
        (directRoute, directIndex) directMember with
    directCarrierCase | directMacrocellCase
  · rcases directCarrierCase with ⟨directCarrier⟩
    exact
      (directOblique
        (directCarrier.finalSegmentAxisAligned
          formula wellFormed degree isLocal
          directLength directLast)).elim
  · rcases directMacrocellCase with ⟨directMacrocell⟩
    have directBounded :
        ∀ point ∈ choice.completeRoute slot,
          InClosedGridRectangle
            (coordinateRadiusLower 288
              (Cell.scale
                (retainedTerminalFanTotalRefinement * 4)
                (PeriodicOrthocrossing.planarSATMacrocellRouteLower
                  directMacrocell.translatedCenter)))
            (coordinateRadiusUpper 288
              (Cell.scale
                (retainedTerminalFanTotalRefinement * 4)
                (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
                  directMacrocell.translatedCenter)))
            point := by
      intro point pointMember
      exact
        choice.completeRoute_point_in_scaledMacrocellRectangle_of_routeEq
          formula wellFormed degree isLocal
          directMacrocell slot choiceRouteEq pointMember
    rcases
        PeriodicOrthocrossing.exists_finalGaugedFlatCarrier_or_macrocellWitness
          formula wellFormed degree isLocal clausesNonempty
          (sourceRoute, sourceIndex) sourceMember with
      sourceCarrierCase | sourceMacrocellCase
    · rcases sourceCarrierCase with ⟨sourceCarrier⟩
      by_cases rectanglesSeparated :
          ClosedGridRectanglesSeparated
            sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
            (PeriodicOrthocrossing.planarSATMacrocellRouteLower
              directMacrocell.translatedCenter)
            (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
              directMacrocell.translatedCenter)
      · exact
          scaledFlatPrefix_strictlyAvoids_directCompleteRoute_of_componentRectanglesSeparated
            (fun point pointMember =>
              sourceCarrier.routePoints_in_rectangle
                formula wellFormed degree isLocal
                (List.mem_of_mem_dropLast pointMember))
            choice slot directBounded rectanglesSeparated
      · exact
          retainedFinalScaledCarrierPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute_of_kind_eq_of_rectangles_not_separated
            formula wellFormed degree isLocal
            sourceCarrier directMacrocell choice slot
            kindEq choiceRouteEq rectanglesSeparated tailAvoid
    · rcases sourceMacrocellCase with ⟨sourceMacrocell⟩
      by_cases centersDifferent :
          sourceMacrocell.translatedCenter ≠
            directMacrocell.translatedCenter
      · exact
          scaledFlatPrefix_strictlyAvoids_directCompleteRoute_of_componentRectanglesSeparated
            (fun point pointMember =>
              sourceMacrocell.routePoints_in_translatedMacrocell
                formula wellFormed degree isLocal
                (List.mem_of_mem_dropLast pointMember))
            choice slot directBounded
            (PeriodicOrthocrossing.planarSATMacrocellRouteRectangles_separated
              centersDifferent)
      · exact equalMacrocells sourceMacrocell directMacrocell
          (not_ne_iff.mp centersDifferent)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

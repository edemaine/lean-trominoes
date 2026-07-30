import LeanTrominoes.RetainedAngularFanSourceRadialSeparation
import LeanTrominoes.RetainedAngularFanOuterRadialPrefixes

/-!
# Transverse separation from a diagonal outer radial fan

For a non-axis-aligned discarded terminal segment, endpoint rectangles are
the wrong clearance certificate.  Instead, use the integral linear
functional perpendicular to its retained primitive direction.

Every outer radial route stays within transverse distance 845 of its
source center.  If an unscaled source prefix lies strictly on either side
of the terminal's supporting line, source-first scaling by a factor whose
combined refinement exceeds 845 converts that integral one-unit gap into
strict route separation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A uniform transverse band containing every point of every retained
outer radial route.  The worst case is the radius-65 coordinate tube around
the routed-clause left-arm normal `(-4, 9)`, whose coefficient norm is 13. -/
theorem retainedTerminalFanOuterRadialRoute_transverse_band
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterRadialRoute
          center terminal slot) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal terminal.1)
          center -
        845 ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal terminal.1)
          point ∧
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal terminal.1)
          point ≤
        Cell.linearValue
            (retainedTerminalFanOuterTransverseNormal terminal.1)
            center +
          845 := by
  have checkpointBound :=
    retainedTerminalFanOuterRadialRoute_point_in_tube
      center terminal slot pointMember
  have sourceBound :=
    inCoordinateCheckpointTube_outerInward_to_sourceTerminal
      65 center terminal slot checkpointBound
  rcases sourceBound with
    ⟨index, _indexBound, nearCheckpoint⟩
  rcases nearCheckpoint.coordinate_bounds with
    ⟨horizontal, vertical⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [Cell.linearValue,
          retainedTerminalFanOuterTransverseNormal,
          RetainedTerminalDirection.primitive,
          OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale]
          at horizontal vertical ⊢ <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [Cell.linearValue,
          retainedTerminalFanOuterTransverseNormal,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive,
          Cell.add, Cell.sub, Cell.scale]
          at horizontal vertical ⊢ <;>
        omega

/-- Strict integral separation of a source prefix from the supporting line
of a retained terminal. -/
def SourcePrefixTransverselySeparated
    (sourceRoute : List Cell)
    (center : Cell)
    (direction : RetainedTerminalDirection) : Prop :=
  (∀ point ∈ sourceRoute.dropLast,
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          point <
        Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          center) ∨
    ∀ point ∈ sourceRoute.dropLast,
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          center <
        Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal direction)
          point

instance
    (sourceRoute : List Cell)
    (center : Cell)
    (direction : RetainedTerminalDirection) :
    Decidable
      (SourcePrefixTransverselySeparated
        sourceRoute center direction) := by
  unfold SourcePrefixTransverselySeparated
  infer_instance

/-- A sufficiently refined source prefix strictly avoids an outer radial
route whenever all of its vertices lie strictly on one side of the
terminal's supporting line. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_transverseSeparated
    {factor : Nat} (factorPositive : 0 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    (sourceRoute : List Cell)
    (referenceCenter : Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (sourceSeparated :
      SourcePrefixTransverselySeparated
        sourceRoute referenceCenter referenceTerminal.1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterRadialRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor referenceCenter))
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot) := by
  let combinedFactor :=
    retainedTerminalFanTotalRefinement * factor
  let normal :=
    retainedTerminalFanOuterTransverseNormal referenceTerminal.1
  let scaledCenter :=
    Cell.scale combinedFactor referenceCenter
  let radialRoute :=
    retainedTerminalFanOuterRadialRoute
      scaledCenter
      (scaleRetainedTerminalData factor referenceTerminal)
      referenceSlot
  have combinedPositive : 0 < combinedFactor := by
    dsimp [combinedFactor]
    exact Nat.mul_pos (by native_decide) factorPositive
  have clearance' : 845 < combinedFactor := by
    simpa [combinedFactor] using clearance
  have combinedPositiveInt :
      (0 : Int) < combinedFactor := by
    exact_mod_cast combinedPositive
  have radialBand :
      ∀ point ∈ radialRoute,
        Cell.linearValue normal scaledCenter - 845 ≤
            Cell.linearValue normal point ∧
          Cell.linearValue normal point ≤
            Cell.linearValue normal scaledCenter + 845 := by
    intro point pointMember
    exact
      retainedTerminalFanOuterRadialRoute_transverse_band
        scaledCenter
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot pointMember
  rcases sourceSeparated with sourceBelow | sourceAbove
  · have separated :=
      routesStrictlyAvoidEachOther_of_linear_separated
        normal
        (Cell.linearValue normal scaledCenter - combinedFactor)
        (first := scalePolyline combinedFactor sourceRoute.dropLast)
        (second := radialRoute)
        (by
          intro point pointMember
          rcases List.mem_map.mp pointMember with
            ⟨sourcePoint, sourcePointMember, rfl⟩
          have original :
              Cell.linearValue normal sourcePoint <
                Cell.linearValue normal referenceCenter := by
            simpa [normal] using
              sourceBelow sourcePoint sourcePointMember
          have integralGap :
              Cell.linearValue normal sourcePoint + 1 ≤
                Cell.linearValue normal referenceCenter := by
            omega
          have scaledGap :=
            mul_le_mul_of_nonneg_left integralGap
              combinedPositiveInt.le
          rw [Cell.linearValue_scale,
            Cell.linearValue_scale]
          rw [mul_add] at scaledGap
          omega)
        (by
          intro point pointMember
          have lower := (radialBand point pointMember).1
          exact lt_of_lt_of_le
            (by omega)
            lower)
    simpa [combinedFactor, normal, scaledCenter, radialRoute,
      scalePolyline_scalePolyline_nat,
      scalePolyline, List.map_map, Function.comp_def,
      Cell.scale_scale, Nat.cast_mul] using separated
  · have separated :=
      routesStrictlyAvoidEachOther_of_linear_separated
        normal
        (Cell.linearValue normal scaledCenter + 845)
        (first := radialRoute)
        (second := scalePolyline combinedFactor sourceRoute.dropLast)
        (fun point pointMember =>
          (radialBand point pointMember).2)
        (by
          intro point pointMember
          rcases List.mem_map.mp pointMember with
            ⟨sourcePoint, sourcePointMember, rfl⟩
          have original :
              Cell.linearValue normal referenceCenter <
                Cell.linearValue normal sourcePoint := by
            simpa [normal] using
              sourceAbove sourcePoint sourcePointMember
          have integralGap :
              Cell.linearValue normal referenceCenter + 1 ≤
                Cell.linearValue normal sourcePoint := by
            omega
          have scaledGap :=
            mul_le_mul_of_nonneg_left integralGap
              combinedPositiveInt.le
          rw [Cell.linearValue_scale,
            Cell.linearValue_scale]
          rw [mul_add] at scaledGap
          omega)
    have symmetric := separated.symm
    simpa [combinedFactor, normal, scaledCenter, radialRoute,
      scalePolyline_scalePolyline_nat,
      scalePolyline, List.map_map, Function.comp_def,
      Cell.scale_scale, Nat.cast_mul] using symmetric

/-- Source-first scaling by four supplies enough clearance for every one of
the eleven retained transverse normals. -/
theorem retainedTerminalFanTotalRefinement_mul_four_gt_transverseBand :
    845 < retainedTerminalFanTotalRefinement * 4 := by
  native_decide

/-- In the final retained drawing, transverse separation is the only new
hypothesis needed to clear another route's complete radial-plus-local fan;
the existing endpoint-contact certificate supplies local-center clearance. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_transverseSeparated
    {Variable : Type*} [DecidableEq Variable]
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
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondCenter : Cell}
    (firstMember :
      (firstRoute, firstIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (secondRoute, secondIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (firstHead : firstRoute.head? = some firstSource)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (sourceNeCenter : firstSource ≠ secondCenter)
    (secondTerminal : RetainedTerminalData)
    (secondSlot : RetainedTerminalSlot)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (transverseSeparated :
      SourcePrefixTransverselySeparated
        firstRoute secondCenter secondTerminal.1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor firstRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor secondCenter))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale factor secondCenter)
  let scaledTerminal :=
    scaleRetainedTerminalData factor secondTerminal
  have factorPositive : 0 < factor := by
    omega
  have radialAvoid :=
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerRadialRoute_of_transverseSeparated
      factorPositive clearance firstRoute secondCenter
      secondTerminal secondSlot transverseSeparated
  have localAvoid :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterLocalRoute
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne firstMember secondMember
      firstLength secondLength indicesDifferent firstHead secondLast
      sourceNeCenter secondTerminal.1 secondSlot
  have scaledLengthPositive : 0 < scaledTerminal.2 := by
    exact scaleRetainedTerminalData_length_pos factorPositive
      (retainedTerminalDirectionClassify_sound secondClassified).1
  have radialAvoid' :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast
        (retainedTerminalFanOuterRadialRoute
          center scaledTerminal secondSlot) := by
    simpa [center, scaledTerminal] using radialAvoid
  have localAvoid' :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast
        (retainedTerminalFanOuterLocalRouteAt
          center scaledTerminal.1 secondSlot) := by
    simpa [center, scaledTerminal] using localAvoid
  rw [retainedTerminalFanOuterCompleteRoute]
  exact
    radialAvoid'.join_right localAvoid'
      (retainedTerminalFanOuterRadialRoute_getLast?
        center scaledTerminal secondSlot scaledLengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center scaledTerminal.1 secondSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

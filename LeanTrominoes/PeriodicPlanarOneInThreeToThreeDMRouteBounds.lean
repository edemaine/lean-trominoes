/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexGeometry
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Coordinate bounds for assembled planar 3DM routes

The source incidence drawing is refined by the standard factor `128` before
local 3DM gadgets are inserted.  This file begins the route-coordinate half
of the global assembly proof: the three central copies of every genuine
source incidence remain in the one-cell halo of the refined fundamental
square.

The proof uses pointwise bounds on the reversed-and-rebased source route.
The `96`, `100`, and `104` lane offsets fit strictly inside the `128` units
of slack created by refining each source grid cell.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-! ## Exhaustive bounds for the finite variable sites -/

/-- Every route point in every one-occurrence variable site lies within one
standard macrocell of the translated site origin. -/
theorem all_oneVariableSiteDrawing_routePointsInMacrocellHalo :
    ∀ kind polarity triple color,
      ((oneVariableSiteDrawing kind polarity).route triple color).all
        (fun point => decide
          (Cell.PositionInMacrocellHalo
            standardThreeStrandLayout.factor
            (Cell.add
              standardThreeStrandLayout.variableOffset point))) = true := by
  native_decide

/-- The analogous exhaustive bound for every two-occurrence variable site. -/
theorem all_twoVariableSiteDrawing_routePointsInMacrocellHalo :
    ∀ firstKind secondKind firstPolarity secondPolarity
        triple color,
      ((twoVariableSiteDrawing firstKind secondKind
        firstPolarity secondPolarity).route triple color).all
        (fun point => decide
          (Cell.PositionInMacrocellHalo
            standardThreeStrandLayout.factor
            (Cell.add
              standardThreeStrandLayout.variableOffset point))) = true := by
  native_decide

/-- The analogous exhaustive bound for every three-occurrence variable
site. -/
theorem all_threeVariableSiteDrawing_routePointsInMacrocellHalo :
    ∀ firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity
        triple color,
      ((threeVariableSiteDrawing firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity).route
          triple color).all
        (fun point => decide
          (Cell.PositionInMacrocellHalo
            standardThreeStrandLayout.factor
            (Cell.add
              standardThreeStrandLayout.variableOffset point))) = true := by
  native_decide

/-- Every element position in every one-occurrence variable site has the
same macrocell-halo bound. -/
theorem all_oneVariableSiteDrawing_elementPositionsInMacrocellHalo :
    ∀ kind polarity element,
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          ((oneVariableSiteDrawing kind polarity).elementPosition
            element)) := by
  native_decide

/-- Element-position bound for all two-occurrence variable sites. -/
theorem all_twoVariableSiteDrawing_elementPositionsInMacrocellHalo :
    ∀ firstKind secondKind firstPolarity secondPolarity element,
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          ((twoVariableSiteDrawing firstKind secondKind
            firstPolarity secondPolarity).elementPosition element)) := by
  native_decide

/-- Element-position bound for all three-occurrence variable sites. -/
theorem all_threeVariableSiteDrawing_elementPositionsInMacrocellHalo :
    ∀ firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity element,
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          ((threeVariableSiteDrawing firstKind secondKind thirdKind
            firstPolarity secondPolarity thirdPolarity)
            |>.elementPosition element)) := by
  native_decide

/-- Every actual finite variable-site route inherits the exhaustive
one-, two-, or three-occurrence macrocell bound. -/
theorem sourceVariableSiteDrawing_routePointsInMacrocellHalo
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    ∀ triple color point,
      point ∈
          (sourceVariableSiteDrawing source atom).route triple color →
        Cell.PositionInMacrocellHalo
          standardThreeStrandLayout.factor
          (Cell.add standardThreeStrandLayout.variableOffset point) := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · unfold sourceVariableSiteDrawing sourceVariableSiteCount
      sourceVariableSiteKind sourceVariableSitePolarity
    rw [one]
    intro triple color point pointMember
    have checked :=
      all_oneVariableSiteDrawing_routePointsInMacrocellHalo
        (occurrenceConnectorKind source atom .first)
        (occurrencePolarity source atom .first)
        triple color
    simp only [List.all_eq_true, decide_eq_true_eq] at checked
    exact checked point pointMember
  · rcases twoOrThree with two | three
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [two]
      intro triple color point pointMember
      have checked :=
        all_twoVariableSiteDrawing_routePointsInMacrocellHalo
          (occurrenceConnectorKind source atom .first)
          (occurrenceConnectorKind source atom .second)
          (occurrencePolarity source atom .first)
          (occurrencePolarity source atom .second)
          triple color
      simp only [List.all_eq_true, decide_eq_true_eq] at checked
      exact checked point pointMember
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [three]
      intro triple color point pointMember
      have checked :=
        all_threeVariableSiteDrawing_routePointsInMacrocellHalo
          (occurrenceConnectorKind source atom .first)
          (occurrenceConnectorKind source atom .second)
          (occurrenceConnectorKind source atom .third)
          (occurrencePolarity source atom .first)
          (occurrencePolarity source atom .second)
          (occurrencePolarity source atom .third)
          triple color
      simp only [List.all_eq_true, decide_eq_true_eq] at checked
      exact checked point pointMember

/-- Every element position of an actual source variable site inherits the
exhaustively checked macrocell bound. -/
theorem sourceVariableSiteDrawing_elementPositionsInMacrocellHalo
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    ∀ element,
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source atom).elementPosition
            element)) := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · unfold sourceVariableSiteDrawing sourceVariableSiteCount
      sourceVariableSiteKind sourceVariableSitePolarity
    rw [one]
    exact all_oneVariableSiteDrawing_elementPositionsInMacrocellHalo
      (occurrenceConnectorKind source atom .first)
      (occurrencePolarity source atom .first)
  · rcases twoOrThree with two | three
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [two]
      exact all_twoVariableSiteDrawing_elementPositionsInMacrocellHalo
        (occurrenceConnectorKind source atom .first)
        (occurrenceConnectorKind source atom .second)
        (occurrencePolarity source atom .first)
        (occurrencePolarity source atom .second)
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [three]
      exact all_threeVariableSiteDrawing_elementPositionsInMacrocellHalo
        (occurrenceConnectorKind source atom .first)
        (occurrenceConnectorKind source atom .second)
        (occurrenceConnectorKind source atom .third)
        (occurrencePolarity source atom .first)
        (occurrencePolarity source atom .second)
        (occurrencePolarity source atom .third)

/-! ## Translated local variable-site prefixes -/

/-- Every point of an ordinary variable-site prefix in the standard
normalized assembly lies inside the refined fundamental square. -/
theorem standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈
        triples source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ assembledOrdinaryPrefix
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        atom slot variant localTriple member color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInFundamentalSquare point := by
  let location :=
    ordinaryTriple_location source.erase atom slot variant
      localTriple member
  unfold assembledOrdinaryPrefix
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, pointEq⟩
  have offsetInside :
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          localPoint) := by
    apply sourceVariableSiteDrawing_routePointsInMacrocellHalo
      source.erase atom location.1
      (activeVariableSiteTriple source.erase atom location.1
        slot location.2.1
        (.ordinary atom slot variant localTriple) location.2.2)
      color localPoint
    simpa [typedVariableSiteRoute] using localPointMember
  have inside :=
    standardMacrocellHaloPosition_inside
      presentation anchorsZero
      (.atom atom) location.1
      (Cell.add standardThreeStrandLayout.variableOffset localPoint)
      offsetInside
  rw [← pointEq]
  simpa [Cell.macrocellPosition, assemblyMacrocellOwnerPosition,
    constructedThreeStrandRouting, constructedVariableOrigin,
    Cell.add, add_assoc] using inside

/-- Every point of a fixed-red variable-site prefix satisfies the same
fundamental-square bound. -/
theorem standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ assembledFixedRedPrefix
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        atom slot localTriple member color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInFundamentalSquare point := by
  let location :=
    fixedRedTriple_location source.erase atom slot localTriple member
  unfold assembledFixedRedPrefix
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, pointEq⟩
  have offsetInside :
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          localPoint) := by
    apply sourceVariableSiteDrawing_routePointsInMacrocellHalo
      source.erase atom location.1
      (activeVariableSiteTriple source.erase atom location.1
        slot location.2.1
        (.fixedRed atom slot localTriple) location.2.2)
      color localPoint
    simpa [typedVariableSiteRoute] using localPointMember
  have inside :=
    standardMacrocellHaloPosition_inside
      presentation anchorsZero
      (.atom atom) location.1
      (Cell.add standardThreeStrandLayout.variableOffset localPoint)
      offsetInside
  rw [← pointEq]
  simpa [Cell.macrocellPosition, assemblyMacrocellOwnerPosition,
    constructedThreeStrandRouting, constructedVariableOrigin,
    Cell.add, add_assoc] using inside

/-! ## Translated clause-core routes -/

/-- Exhaustive coordinate bound for every point of the fixed clause-core
drawing. -/
theorem all_clauseRoutePointsInMacrocellHalo :
    ∀ set color,
      (X3CClauseOrthogonal.route set color).all
        (fun point => decide
          (Cell.PositionInMacrocellHalo
            standardThreeStrandLayout.factor
            (Cell.add
              standardThreeStrandLayout.clauseOffset point))) = true := by
  native_decide

/-- Every translated clause-core route lies inside the standard refined
fundamental square. -/
theorem standardAssembledClauseRoute_pointsInsideFundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet) (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ assembledClauseRoute
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        clauseIndex set color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInFundamentalSquare point := by
  unfold assembledClauseRoute
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, pointEq⟩
  have checked := all_clauseRoutePointsInMacrocellHalo set color
  simp only [List.all_eq_true] at checked
  have offsetInside :
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.clauseOffset
          localPoint) := by
    apply of_decide_eq_true
    apply checked localPoint
    simpa [orientedIncidenceLocalRoute] using localPointMember
  have declared :
      AssemblyMacrocellOwner.IsDeclared source.erase
        (.clause clauseIndex) := by
    simpa [AssemblyMacrocellOwner.IsDeclared,
      PositionedPeriodicCNF.erase] using indexLt
  have inside :=
    standardMacrocellHaloPosition_inside
      presentation anchorsZero
      (.clause clauseIndex) declared
      (Cell.add standardThreeStrandLayout.clauseOffset localPoint)
      offsetInside
  rw [← pointEq]
  simpa [Cell.macrocellPosition, assemblyMacrocellOwnerPosition,
    constructedThreeStrandRouting, constructedClauseOrigin,
    Cell.add, add_assoc] using inside

/-! ## Endpoint detours -/

/-- A canonical five-point detour between two halo points with one unit of
upper margin stays inside the halo. -/
theorem orthogonalDetour_pointsInsideExpandedSquare_of_upperMargin
    {drawing : PeriodicGridDrawing}
    {sourcePoint targetPoint point : Cell}
    (sourceInside :
      drawing.PositionInExpandedSquareWithUpperMargin sourcePoint)
    (targetInside :
      drawing.PositionInExpandedSquareWithUpperMargin targetPoint)
    (pointMember :
      point ∈ PositionedPeriodicCNF.orthogonalDetour
        sourcePoint targetPoint) :
    drawing.PositionInExpandedSquare point := by
  rcases sourcePoint with ⟨sourceX, sourceY⟩
  rcases targetPoint with ⟨targetX, targetY⟩
  simp only
      [PeriodicGridDrawing.PositionInExpandedSquareWithUpperMargin]
    at sourceInside targetInside
  simp [PositionedPeriodicCNF.orthogonalDetour] at pointMember
  rcases pointMember with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp_all [PeriodicGridDrawing.PositionInExpandedSquare,
      PositionedPeriodicCNF.freshDetourCoordinate]
    omega

/-- The canonical five-point orthogonal detour between two points in the
fundamental square remains in the surrounding one-cell halo. -/
theorem orthogonalDetour_pointsInsideExpandedSquare_of_fundamental
    {drawing : PeriodicGridDrawing}
    {sourcePoint targetPoint point : Cell}
    (sourceInside :
      drawing.PositionInFundamentalSquare sourcePoint)
    (targetInside :
      drawing.PositionInFundamentalSquare targetPoint)
    (pointMember :
      point ∈ PositionedPeriodicCNF.orthogonalDetour
        sourcePoint targetPoint) :
    drawing.PositionInExpandedSquare point := by
  exact
    orthogonalDetour_pointsInsideExpandedSquare_of_upperMargin
      (PeriodicGridDrawing.positionInExpandedSquareWithUpperMargin_of_fundamental
        sourceInside)
      (PeriodicGridDrawing.positionInExpandedSquareWithUpperMargin_of_fundamental
        targetInside)
      pointMember

/-- The temporary RGB port at the variable end of a routed occurrence lies
inside the standard assembled fundamental square. -/
theorem standardRoutedVariablePort_insideFundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInFundamentalSquare
        (Cell.add
          (constructedVariableOrigin placement
            standardThreeStrandLayout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) := by
  let drawing :=
    sourceVariableSiteDrawing source.erase entry.1.1
  let active :=
    routedActiveVariableSiteTriple source.erase entry color
  have offsetInside :
      Cell.PositionInMacrocellHalo
        standardThreeStrandLayout.factor
        (Cell.add standardThreeStrandLayout.variableOffset
          (drawing.elementPosition
            (drawing.reference active color))) := by
    exact
      sourceVariableSiteDrawing_elementPositionsInMacrocellHalo
        source.erase entry.1.1 entry.atom_mem
        (drawing.reference active color)
  have inside :=
    standardMacrocellHaloPosition_inside
      presentation anchorsZero
      (.atom entry.1.1) entry.atom_mem
      (Cell.add standardThreeStrandLayout.variableOffset
        (drawing.elementPosition
          (drawing.reference active color)))
      offsetInside
  simpa [drawing, active, routedVariablePortPosition,
    Cell.macrocellPosition, assemblyMacrocellOwnerPosition,
    constructedVariableOrigin, Cell.add, add_assoc] using inside

/-- The first point of the refined central lane lies in the variable
macrocell and hence in the fundamental square. -/
theorem standardOccurrenceLaneStart_insideFundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := occurrenceSpliceData presentation entry
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInFundamentalSquare
        (Cell.add
          (standardThreeStrandLayout.laneOffset color)
          (Cell.scale standardThreeStrandLayout.factor
            (placement.position data.tagged.1.atom))) := by
  let data := occurrenceSpliceData presentation entry
  have atomEq : data.tagged.1.atom = entry.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase entry.1.1 entry.1.2 data.tagged
      data.occurrenceLookup).2
  have offsetInside :
      Cell.PositionInOpenMacrocell
        standardThreeStrandLayout.factor
        (standardThreeStrandLayout.laneOffset color) := by
    cases color <;>
      norm_num [Cell.PositionInOpenMacrocell,
        standardThreeStrandLayout]
  have inside :=
    standardMacrocellPosition_inside
      presentation anchorsZero
      (.atom entry.1.1) entry.atom_mem
      (standardThreeStrandLayout.laneOffset color)
      offsetInside
  change
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInFundamentalSquare
        (Cell.add
          (standardThreeStrandLayout.laneOffset color)
          (Cell.scale standardThreeStrandLayout.factor
            (placement.position data.tagged.1.atom)))
  rw [atomEq]
  simpa [Cell.macrocellPosition, assemblyMacrocellOwnerPosition,
    Cell.add, add_comm] using inside

/-- Every point of the variable-end orthogonal stub lies in the assembled
one-cell halo. -/
theorem standardOccurrenceVariableStub_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceVariableStub
        presentation standardThreeStrandLayout entry color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  let data := occurrenceSpliceData presentation entry
  unfold occurrenceVariableStub at pointMember
  apply
    orthogonalDetour_pointsInsideExpandedSquare_of_fundamental
      (drawing := assembledDrawing
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout))
      (standardRoutedVariablePort_insideFundamentalSquare
        presentation anchorsZero entry color)
      (standardOccurrenceLaneStart_insideFundamentalSquare
        presentation anchorsZero entry color)
      pointMember

/-- Scaling a halo-bounded source point by the standard refinement factor and
adding a nonnegative local offset with one unit of upper slack preserves a
one-unit upper margin in the refined halo. -/
theorem standardRefinedPoint_insideExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    {sourcePoint localOffset : Cell}
    (sourcePointInside :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes)
        |>.PositionInExpandedSquare sourcePoint)
    (localOffsetInside :
      0 ≤ localOffset.1 ∧
        localOffset.1 + 1 < standardThreeStrandLayout.factor ∧
        0 ≤ localOffset.2 ∧
        localOffset.2 + 1 < standardThreeStrandLayout.factor) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquareWithUpperMargin
        (Cell.add localOffset
          (Cell.scale standardThreeStrandLayout.factor sourcePoint)) := by
  simp only [PeriodicGridDrawing.PositionInExpandedSquare]
    at sourcePointInside
  simp only
    [PeriodicGridDrawing.PositionInExpandedSquareWithUpperMargin]
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    source placement presentation.routes presentation.periodPositive]
    at sourcePointInside
  rw [assembledDrawing_gridSize]
  rcases sourcePoint with ⟨sourceX, sourceY⟩
  rcases localOffset with ⟨offsetX, offsetY⟩
  simp [constructedThreeStrandRouting, standardThreeStrandLayout,
    Cell.add, Cell.scale] at localOffsetInside ⊢
  omega

/-- Every standard lane offset satisfies the refined upper-margin
hypothesis. -/
theorem standardLanePoint_insideExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    {sourcePoint : Cell}
    (sourcePointInside :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes)
        |>.PositionInExpandedSquare sourcePoint)
    (color : WireColor) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquareWithUpperMargin
        (Cell.add
          (standardThreeStrandLayout.laneOffset color)
          (Cell.scale standardThreeStrandLayout.factor sourcePoint)) := by
  apply standardRefinedPoint_insideExpandedSquareWithUpperMargin
    presentation sourcePointInside
  cases color <;>
    norm_num [standardThreeStrandLayout]

/-- Scaling a halo-bounded source point by the standard refinement factor and
adding any of the three standard lane offsets keeps it in the refined halo. -/
theorem standardLanePoint_insideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    {sourcePoint : Cell}
    (sourcePointInside :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes)
        |>.PositionInExpandedSquare sourcePoint)
    (color : WireColor) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare
        (Cell.add
          (standardThreeStrandLayout.laneOffset color)
          (Cell.scale standardThreeStrandLayout.factor sourcePoint)) := by
  exact PeriodicGridDrawing.positionInExpandedSquare_of_upperMargin
    (standardLanePoint_insideExpandedSquareWithUpperMargin
      presentation sourcePointInside color)

/-- Every point on every refined central incidence lane lies in the open
one-cell halo of the assembled drawing. -/
theorem standardOccurrenceLaneRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceLaneRoute
        presentation standardThreeStrandLayout entry color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  let data := occurrenceSpliceData presentation entry
  change point ∈
    PeriodicOrthocrossing.translatePolyline
      (standardThreeStrandLayout.laneOffset color)
      (scalePolyline standardThreeStrandLayout.factor
        (presentation.variableToClauseRoute data.indexed.1))
    at pointMember
  unfold PeriodicOrthocrossing.translatePolyline
    scalePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨scaledPoint, scaledPointMember, pointEq⟩
  rcases List.mem_map.mp scaledPointMember with
    ⟨sourcePoint, sourcePointMember, scaledPointEq⟩
  subst scaledPoint
  subst point
  apply standardLanePoint_insideExpandedSquare presentation
  exact sourceBounds data.indexed data.indexedMember
    sourcePoint sourcePointMember

/-- The clause-end point of a refined central lane retains the one-unit
upper margin needed by the following orthogonal stub. -/
theorem standardOccurrenceLaneEnd_insideExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := occurrenceSpliceData presentation entry
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquareWithUpperMargin
        (Cell.add
          (standardThreeStrandLayout.laneOffset color)
          (Cell.scale standardThreeStrandLayout.factor
            (PositionedPeriodicCNF.variableToClauseTarget
              placement data.positionedClause data.tagged.1))) := by
  let data := occurrenceSpliceData presentation entry
  have targetMember :
      PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1 ∈
        presentation.variableToClauseRoute data.indexed.1 :=
    mem_of_getLast?_eq_some data.routeLast
  have targetInside :=
    sourceBounds data.indexed data.indexedMember
      (PositionedPeriodicCNF.variableToClauseTarget
        placement data.positionedClause data.tagged.1)
      targetMember
  exact standardLanePoint_insideExpandedSquareWithUpperMargin
    presentation targetInside color

/-- Every clause-terminal local offset has ample room below the upper edge
of the standard `128 × 128` macrocell. -/
theorem routedClauseLocalOffset_hasUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    let offset :=
      Cell.add standardThreeStrandLayout.clauseOffset
        (routedClausePortPosition source entry color)
    0 ≤ offset.1 ∧
      offset.1 + 1 < standardThreeStrandLayout.factor ∧
      0 ≤ offset.2 ∧
      offset.2 + 1 < standardThreeStrandLayout.factor := by
  cases color <;>
    simp only [routedClausePortPosition]
  all_goals
    cases groupEq :
      terminalGroupOfLiteralIndex
        (occurrenceLiteralIndex source entry.1.1 entry.1.2) <;>
      norm_num [standardThreeStrandLayout,
        redClauseTerminal, greenClauseTerminal, blueClauseTerminal,
        redClauseElementLocalPosition,
        greenClauseElementLocalPosition,
        blueClauseElementLocalPosition,
        terminalElementForColor,
        X3CClauseTerminal.attachmentElement,
        X3CClauseOrthogonal.elementPosition,
        Cell.add, groupEq]

/-- Under the standard layout, the routed clause terminal is the refined
source clause endpoint plus its checked local clause-port offset. -/
theorem standardRoutedClauseTarget_eq_refinedSourceTarget
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := occurrenceSpliceData presentation entry
    routedClauseTargetPosition source.erase
        (standardThreeStrandLayout.factor * placement.period)
        (constructedClauseOrigin source standardThreeStrandLayout)
        entry color =
      Cell.add
        (Cell.add standardThreeStrandLayout.clauseOffset
          (routedClausePortPosition source.erase entry color))
        (Cell.scale standardThreeStrandLayout.factor
          (PositionedPeriodicCNF.variableToClauseTarget
            placement data.positionedClause data.tagged.1)) := by
  let data := occurrenceSpliceData presentation entry
  have occurrenceClauseEq :
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2 =
        data.indexed.1.clauseIndex := by
    calc
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2 =
          data.tagged.2.1 :=
        occurrenceClauseIndex_of_occurrenceAt
          source.erase entry.1.1 entry.1.2
          data.tagged data.occurrenceLookup
      _ = data.indexed.1.clauseIndex := by
        have metadata :=
          congrArg (fun tagged => tagged.2.1) data.metadataEq
        simpa [incidenceTaggedOccurrence] using metadata.symm
  have occurrenceOffsetEq :
      occurrenceReverseOffset source.erase entry.1.1 entry.1.2 =
        PeriodicOneInThreeToThreeDM.reverseOffset
          data.tagged.1.offset :=
    occurrenceReverseOffset_of_occurrenceAt
      source.erase entry.1.1 entry.1.2
      data.tagged data.occurrenceLookup
  have indexLt :
      data.indexed.1.clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx data.clauseMember
  have positionedClauseEq :
      source.clauses[data.indexed.1.clauseIndex] =
        data.positionedClause :=
    (List.mem_zipIdx' data.clauseMember).2.symm
  change
    routedClauseTargetPosition source.erase
        (standardThreeStrandLayout.factor * placement.period)
        (constructedClauseOrigin source standardThreeStrandLayout)
        entry color =
      Cell.add
        (Cell.add standardThreeStrandLayout.clauseOffset
          (routedClausePortPosition source.erase entry color))
        (Cell.scale standardThreeStrandLayout.factor
          (PositionedPeriodicCNF.variableToClauseTarget
            placement data.positionedClause data.tagged.1))
  unfold routedClauseTargetPosition
  rw [occurrenceClauseEq, occurrenceOffsetEq]
  simp [constructedClauseOrigin,
    positionedClausePositionAt,
    List.getElem?_eq_getElem indexLt, positionedClauseEq,
    PositionedPeriodicCNF.variableToClauseTarget,
    PeriodicOneInThreeToThreeDM.reverseOffset,
    PeriodicVariablePlacement.translation,
    standardThreeStrandLayout, Cell.add, Cell.scale]
  constructor <;> ring

/-- The actual routed clause-terminal endpoint retains the same upper-margin
halo bound as the refined source clause endpoint. -/
theorem standardRoutedClauseTarget_insideExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquareWithUpperMargin
        (routedClauseTargetPosition source.erase
          (standardThreeStrandLayout.factor * placement.period)
          (constructedClauseOrigin source standardThreeStrandLayout)
          entry color) := by
  let data := occurrenceSpliceData presentation entry
  have targetMember :
      PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1 ∈
        presentation.variableToClauseRoute data.indexed.1 :=
    mem_of_getLast?_eq_some data.routeLast
  have sourceTargetInside :=
    sourceBounds data.indexed data.indexedMember
      (PositionedPeriodicCNF.variableToClauseTarget
        placement data.positionedClause data.tagged.1)
      targetMember
  have refinedInside :=
    standardRefinedPoint_insideExpandedSquareWithUpperMargin
      presentation sourceTargetInside
      (routedClauseLocalOffset_hasUpperMargin
        source.erase entry color)
  rw [standardRoutedClauseTarget_eq_refinedSourceTarget
    presentation entry color]
  exact refinedInside

/-- Every point of the clause-end orthogonal stub lies in the assembled
one-cell halo. -/
theorem standardOccurrenceClauseStub_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceClauseStub
        presentation standardThreeStrandLayout entry color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  unfold occurrenceClauseStub at pointMember
  apply
    orthogonalDetour_pointsInsideExpandedSquare_of_upperMargin
      (drawing := assembledDrawing
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout))
      (standardOccurrenceLaneEnd_insideExpandedSquareWithUpperMargin
        presentation sourceBounds entry color)
      (standardRoutedClauseTarget_insideExpandedSquareWithUpperMargin
        presentation sourceBounds entry color)
      pointMember

/-- Every point of a complete standard three-strand corridor lies in the
assembled one-cell halo. -/
theorem standardConstructedThreeStrandRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ constructedThreeStrandRoute
        presentation standardThreeStrandLayout entry color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  unfold constructedThreeStrandRoute at pointMember
  rcases mem_joinAtEndpoint pointMember with
    firstTwoMember | clauseStubMember
  · rcases mem_joinAtEndpoint firstTwoMember with
      variableStubMember | laneMember
    · exact standardOccurrenceVariableStub_pointsInsideExpandedSquare
        presentation anchorsZero entry color variableStubMember
    · exact standardOccurrenceLaneRoute_pointsInsideExpandedSquare
        presentation sourceBounds entry color laneMember
  · exact standardOccurrenceClauseStub_pointsInsideExpandedSquare
      presentation sourceBounds entry color clauseStubMember

/-! ## Complete assembled route list -/

/-- Every point of every standard assembled typed incidence route lies in
the one-cell halo. -/
theorem standardAssembledTypedIncidenceRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (triple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ assembledTypedIncidenceRoute
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        triple color) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  unfold assembledTypedIncidenceRoute at pointMember
  split at pointMember
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈
          triples source.erase :=
      tripleEq ▸ triple.2
    let location :=
      ordinaryTriple_location source.erase atom slot variant
        localTriple member
    split at pointMember
    next routed =>
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff
            source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      rcases mem_joinAtEndpoint pointMember with
        prefixMember | corridorMember
      · exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
          (standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
            presentation anchorsZero atom slot variant localTriple
            member color prefixMember)
      · apply standardConstructedThreeStrandRoute_pointsInsideExpandedSquare
          presentation anchorsZero sourceBounds entry color
        simpa [constructedThreeStrandRouting] using corridorMember
    next notRouted =>
      exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
        (standardAssembledOrdinaryPrefix_pointsInsideFundamentalSquare
          presentation anchorsZero atom slot variant localTriple
          member color pointMember)
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈ triples source.erase :=
      tripleEq ▸ triple.2
    let location :=
      fixedRedTriple_location source.erase atom slot localTriple member
    split at pointMember
    next routed =>
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff
            source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      rcases mem_joinAtEndpoint pointMember with
        prefixMember | corridorMember
      · exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
          (standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
            presentation anchorsZero atom slot localTriple
            member color prefixMember)
      · apply standardConstructedThreeStrandRoute_pointsInsideExpandedSquare
          presentation anchorsZero sourceBounds entry color
        simpa [constructedThreeStrandRouting] using corridorMember
    next notRouted =>
      exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
        (standardAssembledFixedRedPrefix_pointsInsideFundamentalSquare
          presentation anchorsZero atom slot localTriple
          member color pointMember)
  next clauseIndex set tripleEq =>
    have member :
        Triple.clause (Variable := Variable) clauseIndex set ∈
          triples source.erase :=
      tripleEq ▸ triple.2
    have declared :=
      tripleMacrocellOwner_declared source.erase
        (.clause clauseIndex set) member
    have indexLt : clauseIndex < source.clauses.length := by
      simpa [tripleMacrocellOwner,
        AssemblyMacrocellOwner.IsDeclared,
        PositionedPeriodicCNF.erase] using declared
    exact PeriodicGridDrawing.positionInExpandedSquare_of_fundamental
      (standardAssembledClauseRoute_pointsInsideFundamentalSquare
        presentation anchorsZero clauseIndex indexLt set color
        pointMember)

/-- Every total tag-selected standard route, including its unreachable empty
fallback, is pointwise halo-bounded. -/
theorem standardAssembledRouteAtTag_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (tag : PeriodicThreeDM.IncidenceTag)
    {point : Cell}
    (pointMember :
      point ∈ assembledRouteAtTag
        (constructedThreeStrandRouting
          presentation standardThreeStrandLayout)
        tag) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.PositionInExpandedSquare point := by
  unfold assembledRouteAtTag at pointMember
  split at pointMember
  next indexLt =>
    exact standardAssembledTypedIncidenceRoute_pointsInsideExpandedSquare
      presentation anchorsZero sourceBounds
      ⟨(triples source.erase)[tag.tripleIndex]'indexLt,
        List.getElem_mem indexLt⟩
      tag.color pointMember
  next indexNotLt =>
    simp at pointMember

/-- The complete standard assembled route list is pointwise halo-bounded. -/
theorem standardAssembledRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.RoutePointsInExpandedSquare := by
  intro route routeMember point pointMember
  change route ∈
    assembledEdgeRoutes
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout)
    at routeMember
  unfold assembledEdgeRoutes at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨tag, tagMember, routeEq⟩
  subst route
  exact standardAssembledRouteAtTag_pointsInsideExpandedSquare
    presentation anchorsZero sourceBounds tag pointMember

/-- Consequently all indexed segment endpoints of the standard assembled
drawing lie in the one-cell halo required by the expanded finite checker. -/
theorem standardAssembledSegmentEndpointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare) :
    (assembledDrawing
      (constructedThreeStrandRouting
        presentation standardThreeStrandLayout))
      |>.SegmentEndpointsInExpandedSquare :=
  PeriodicGridDrawing.segmentEndpointsInExpandedSquare_of_routePoints
    (standardAssembledRoutePointsInExpandedSquare
      presentation anchorsZero sourceBounds)

/-- For an arbitrary halo-bounded source presentation, anchor normalization
supplies the canonical standard three-strand routing used by the remaining
finite checks. -/
noncomputable def standardNormalizedThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedContinuousPlanarIncidencePresentation placement) :
    ThreeStrandRouting
      (normalizedPositionedSource source placement).erase :=
  constructedThreeStrandRouting
    (normalizedHaloBoundedIncidencePresentation presentation
      |>.toPlanarIncidencePresentation)
    standardThreeStrandLayout

/-- Anchor normalization supplies all hypotheses of the standard assembled
endpoint theorem. -/
theorem standardNormalizedAssembledSegmentEndpointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedContinuousPlanarIncidencePresentation placement) :
    (assembledDrawing
      (standardNormalizedThreeStrandRouting presentation))
      |>.SegmentEndpointsInExpandedSquare := by
  let normalized :=
    normalizedHaloBoundedIncidencePresentation presentation
  change
    (assembledDrawing
      (constructedThreeStrandRouting
        normalized.toPlanarIncidencePresentation
        standardThreeStrandLayout))
      |>.SegmentEndpointsInExpandedSquare
  exact
    standardAssembledSegmentEndpointsInExpandedSquare
      normalized.toPlanarIncidencePresentation
      (normalizedPositionedSource_hasZeroClauseAnchors
        source placement)
      normalized.rebasedRoutePointsInside

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseOtherTargetSeparation

/-!
# Cross-clause direct routes at one target center

Two incidences from different local clauses can converge on the same
variable center.  Their occurrence slots are not arbitrary: the angular
occurrence order assigns increasing slots to nondecreasing retained terminal
directions.  This file isolates that order-compatible local geometry for the
crossover and duplicator atlases.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- The two slots follow one of the two possible strict orders, and the
atlas direction ranks are nondecreasing in that same order. -/
def RetainedDirectSourceRouteChoice.AngularOrderCompatible
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot) : Prop :=
  let firstDirection :=
    (retainedDirectSourcePrefixChoiceAt
      first.kind first.index).direction
  let secondDirection :=
    (retainedDirectSourcePrefixChoiceAt
      second.kind second.index).direction
  (firstSlot.val < secondSlot.val ∧
      firstDirection.angularRank ≤ secondDirection.angularRank) ∨
    (secondSlot.val < firstSlot.val ∧
      secondDirection.angularRank ≤ firstDirection.angularRank)

instance
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    Decidable
      (first.AngularOrderCompatible
        second firstSlot secondSlot) := by
  unfold RetainedDirectSourceRouteChoice.AngularOrderCompatible
  infer_instance

/-- The five pieces of a complete direct route, from its source escape
through its Figure 7 spoke. -/
inductive RetainedDirectSourceSameTargetComponent
  | escape
  | laneShift
  | remainingRay
  | localAdapter
  | figure7Spoke
  deriving DecidableEq, Fintype, Repr

/-- The refined Figure 7 spoke translated so that its macrocell is centered
at `center`. -/
def retainedTerminalFanFigure7SpokeAt
    (center : Cell)
    (slot : RetainedTerminalSlot) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (Cell.sub center
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
    (scalePolyline
      retainedTerminalFanRoutingRefinement
      (OccurrenceSplitRing.spokeRoute
        (angularPortOfIndex slot.val)))

/-- An earlier local adapter strictly avoids a later Figure 7 spoke at the
origin.  This is the small finite boundary-interface certificate. -/
theorem
    retainedTerminalFanOuterLocalRoute_strictlyAvoid_laterFigure7Spoke :
    ∀ (direction : RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstSlot.val < secondSlot.val →
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterLocalRouteAt
          (0, 0) direction firstSlot)
        (retainedTerminalFanFigure7SpokeAt
          (0, 0) secondSlot) := by
  native_decide

/-- An earlier Figure 7 spoke strictly avoids a later local adapter at the
origin.  This is the reverse boundary-interface certificate. -/
theorem
    retainedTerminalFanFigure7Spoke_strictlyAvoid_laterOuterLocalRoute :
    ∀ (direction : RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstSlot.val < secondSlot.val →
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanFigure7SpokeAt
          (0, 0) firstSlot)
        (retainedTerminalFanOuterLocalRouteAt
          (0, 0) direction secondSlot) := by
  native_decide

/-- Translating the origin-centered local adapter positions it at `center`. -/
theorem retainedTerminalFanOuterLocalRouteAt_zero_map_add
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterLocalRouteAt
      (0, 0) direction slot).map (Cell.add center) =
        retainedTerminalFanOuterLocalRouteAt
          center direction slot := by
  unfold retainedTerminalFanOuterLocalRouteAt
  rw [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add]

/-- Translating the origin-centered refined spoke positions it at `center`. -/
theorem retainedTerminalFanFigure7SpokeAt_zero_map_add
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanFigure7SpokeAt
      (0, 0) slot).map (Cell.add center) =
        retainedTerminalFanFigure7SpokeAt center slot := by
  unfold retainedTerminalFanFigure7SpokeAt
    PeriodicOrthocrossing.translatePolyline
  rw [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- The local-adapter/spoke certificate is translation invariant. -/
theorem
    retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_laterFigure7SpokeAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterLocalRouteAt
        center direction firstSlot)
      (retainedTerminalFanFigure7SpokeAt
        center secondSlot) := by
  have translated :=
    (retainedTerminalFanOuterLocalRoute_strictlyAvoid_laterFigure7Spoke
      direction firstSlot secondSlot slotsLt).map_add center
  rw [retainedTerminalFanOuterLocalRouteAt_zero_map_add,
    retainedTerminalFanFigure7SpokeAt_zero_map_add] at translated
  exact translated

/-- The spoke/local-adapter certificate is translation invariant. -/
theorem
    retainedTerminalFanFigure7SpokeAt_strictlyAvoid_laterOuterLocalRouteAt
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanFigure7SpokeAt
        center firstSlot)
      (retainedTerminalFanOuterLocalRouteAt
        center direction secondSlot) := by
  have translated :=
    (retainedTerminalFanFigure7Spoke_strictlyAvoid_laterOuterLocalRoute
      direction firstSlot secondSlot slotsLt).map_add center
  rw [retainedTerminalFanFigure7SpokeAt_zero_map_add,
    retainedTerminalFanOuterLocalRouteAt_zero_map_add] at translated
  exact translated

/-- Ordered slots select distinct, strictly separated Figure 7 spokes at a
common refined fan center. -/
theorem retainedTerminalFanFigure7SpokesAt_strictlyAvoid
    (center : Cell)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanFigure7SpokeAt center firstSlot)
      (retainedTerminalFanFigure7SpokeAt center secondSlot) := by
  have indicesDifferent : firstSlot.val ≠ secondSlot.val :=
    Nat.ne_of_lt slotsLt
  have localAvoid :=
    OccurrenceSplitRing.spokeRoutes_strictlyAvoid_of_indices_ne
      firstSlot.val secondSlot.val firstSlot.isLt secondSlot.isLt
      indicesDifferent
  have scaled :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanRoutingRefinement
          (OccurrenceSplitRing.spokeRoute
            (angularPortOfIndex firstSlot.val)))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (OccurrenceSplitRing.spokeRoute
            (angularPortOfIndex secondSlot.val))) :=
    RoutesStrictlyAvoidEachOther.scalePolyline
      (factor := retainedTerminalFanRoutingRefinement)
      (by simp [retainedTerminalFanRoutingRefinement])
      localAvoid
  simpa [retainedTerminalFanFigure7SpokeAt,
    PeriodicOrthocrossing.translatePolyline] using
      scaled.map_add
        (Cell.sub center
          (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))

/-- One of the five pieces of a local direct route. -/
def retainedDirectSourceSameTargetComponentRoute
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (component : RetainedDirectSourceSameTargetComponent) :
    List Cell :=
  let center :=
    retainedDirectSourceFanCenterAt choice.kind choice.index
  let terminal :=
    retainedDirectSourceFanTerminalAt choice.kind choice.index
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  match component with
  | .escape =>
      (retainedDirectSourceFanEscapeAt
        choice.kind choice.index slot).route
  | .laneShift =>
      retainedTerminalFanOuterLaneShiftRouteAt
        escapePoint terminal.1 slot
  | .remainingRay =>
      (retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
        shiftedEscapePoint
  | .localAdapter =>
      retainedTerminalFanOuterLocalRouteAt
        center terminal.1 slot
  | .figure7Spoke =>
      retainedDirectSourceFigure7SpokeAt
        choice.kind choice.index slot

/-- Local-adapter/local-adapter and adapter/spoke interactions are proved by
generic angular-fan lemmas.  Every other ordered component pair uses a finite
atlas certificate. -/
def retainedDirectSourceSameTargetUsesAtlasCertificate
    (first second : RetainedDirectSourceSameTargetComponent) : Bool :=
  match first, second with
  | .localAdapter, .localAdapter => false
  | .localAdapter, .figure7Spoke => false
  | .figure7Spoke, .localAdapter => false
  | .figure7Spoke, .figure7Spoke => false
  | _, _ => true

/-- The four most common transverse/radial mixtures, kept ahead of the
biased family so native evaluation usually stops quickly. -/
def retainedDirectSourceSameTargetCrossNormals
    (first second : RetainedDirectSourceRouteChoice) : List Cell :=
  let firstPrimitive :=
    retainedDirectSourceCrossClausePrimitive first
  let secondPrimitive :=
    retainedDirectSourceCrossClausePrimitive second
  let firstTurn := rotateCellQuarterTurn firstPrimitive
  let secondTurn := rotateCellQuarterTurn secondPrimitive
  (List.range 13).flatMap fun weight =>
    [Cell.add (Cell.scale weight firstTurn) secondPrimitive,
      Cell.add firstTurn (Cell.scale weight secondPrimitive),
      Cell.add (Cell.scale weight secondTurn) firstPrimitive,
      Cell.add secondTurn (Cell.scale weight firstPrimitive)]

/-- The fast separator normals biased in both directions between the two
terminal primitives. -/
def retainedDirectSourceSameTargetBiasedNormals
    (first second : RetainedDirectSourceRouteChoice) : List Cell :=
  let firstPrimitive :=
    retainedDirectSourceCrossClausePrimitive first
  let secondPrimitive :=
    retainedDirectSourceCrossClausePrimitive second
  let firstEarlier :=
    (retainedDirectSourcePrefixChoiceAt
      first.kind first.index).direction.angularRank <
    (retainedDirectSourcePrefixChoiceAt
      second.kind second.index).direction.angularRank
  let earlier := if firstEarlier then firstPrimitive else secondPrimitive
  let later := if firstEarlier then secondPrimitive else firstPrimitive
  retainedDirectSourceCrossClauseCandidateNormals first second ++
    [earlier, later,
      rotateCellQuarterTurn earlier,
      rotateCellQuarterTurn later,
      rotateCellQuarterTurn
        (Cell.add (Cell.scale 2 earlier) later),
      rotateCellQuarterTurn
        (Cell.add (Cell.scale 3 earlier) later),
      rotateCellQuarterTurn
        (Cell.add (Cell.scale 4 earlier) later),
      rotateCellQuarterTurn
        (Cell.add (Cell.scale 8 earlier) later),
      rotateCellQuarterTurn
        (Cell.add earlier (Cell.scale 2 later)),
      rotateCellQuarterTurn
        (Cell.add earlier (Cell.scale 3 later)),
      rotateCellQuarterTurn
        (Cell.add earlier (Cell.scale 4 later)),
      rotateCellQuarterTurn
        (Cell.add earlier (Cell.scale 8 later))]

/-- A tiered linear certificate: most pairs use a biased angular normal,
while the exceptional cross-component envelopes use a transverse/radial
primitive mixture. -/
def retainedDirectSourceSameTargetComponentsLinearlySeparated
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstComponent secondComponent :
      RetainedDirectSourceSameTargetComponent) : Prop :=
  let firstRoute :=
    retainedDirectSourceSameTargetComponentRoute
      first firstSlot firstComponent
  let secondRoute :=
    retainedDirectSourceSameTargetComponentRoute
      second secondSlot secondComponent
  RoutesLinearlySeparatedBySome
      (retainedDirectSourceSameTargetBiasedNormals first second)
      firstRoute secondRoute ∨
    RoutesLinearlySeparatedBySome
      (retainedDirectSourceSameTargetCrossNormals first second)
      firstRoute secondRoute

instance
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstComponent secondComponent :
      RetainedDirectSourceSameTargetComponent) :
    Decidable
      (retainedDirectSourceSameTargetComponentsLinearlySeparated
        first second firstSlot secondSlot firstComponent secondComponent) := by
  unfold retainedDirectSourceSameTargetComponentsLinearlySeparated
  infer_instance

/-- Either tier of the component-envelope certificate gives exact continuous
route separation. -/
theorem
    routesStrictlyAvoidEachOther_of_sameTargetComponentsLinearlySeparated
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstComponent secondComponent :
      RetainedDirectSourceSameTargetComponent)
    (separated :
      retainedDirectSourceSameTargetComponentsLinearlySeparated
        first second firstSlot secondSlot
        firstComponent secondComponent) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceSameTargetComponentRoute
        first firstSlot firstComponent)
      (retainedDirectSourceSameTargetComponentRoute
        second secondSlot secondComponent) := by
  unfold retainedDirectSourceSameTargetComponentsLinearlySeparated
    at separated
  rcases separated with biased | cross
  · exact
      routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
        (retainedDirectSourceSameTargetBiasedNormals first second)
        _ _ biased
  · exact
      routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
        (retainedDirectSourceSameTargetCrossNormals first second)
        _ _ cross

/-- Pairwise component separation combines the finite source-side envelope
with the four reusable common-center fan cases. -/
theorem retainedDirectSourceSameTargetComponentRoutes_strictlyAvoid
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsLe :
      (retainedDirectSourcePrefixChoiceAt
          first.kind first.index).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          second.kind second.index).direction.angularRank)
    (centersEqual :
      retainedDirectSourceFanCenterAt first.kind first.index =
        retainedDirectSourceFanCenterAt second.kind second.index)
    (atlasCertificate :
      ∀ firstComponent secondComponent,
        retainedDirectSourceSameTargetUsesAtlasCertificate
            firstComponent secondComponent = true →
          retainedDirectSourceSameTargetComponentsLinearlySeparated
            first second firstSlot secondSlot
            firstComponent secondComponent)
    (firstComponent secondComponent :
      RetainedDirectSourceSameTargetComponent) :
    RoutesStrictlyAvoidEachOther
      (retainedDirectSourceSameTargetComponentRoute
        first firstSlot firstComponent)
      (retainedDirectSourceSameTargetComponentRoute
        second secondSlot secondComponent) := by
  by_cases usesAtlas :
      retainedDirectSourceSameTargetUsesAtlasCertificate
          firstComponent secondComponent = true
  · exact
      routesStrictlyAvoidEachOther_of_sameTargetComponentsLinearlySeparated
        first second firstSlot secondSlot firstComponent secondComponent
        (atlasCertificate firstComponent secondComponent usesAtlas)
  · have fanCases :
        (firstComponent = .localAdapter ∧
            secondComponent = .localAdapter) ∨
          (firstComponent = .localAdapter ∧
            secondComponent = .figure7Spoke) ∨
          (firstComponent = .figure7Spoke ∧
            secondComponent = .localAdapter) ∨
          (firstComponent = .figure7Spoke ∧
            secondComponent = .figure7Spoke) := by
      cases firstComponent <;> cases secondComponent <;>
        simp_all [retainedDirectSourceSameTargetUsesAtlasCertificate]
    rcases fanCases with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterLocalRouteAt
            (retainedDirectSourceFanCenterAt first.kind first.index)
            (retainedDirectSourcePrefixChoiceAt
              first.kind first.index).direction firstSlot)
          (retainedTerminalFanOuterLocalRouteAt
            (retainedDirectSourceFanCenterAt second.kind second.index)
            (retainedDirectSourcePrefixChoiceAt
              second.kind second.index).direction secondSlot)
      rw [← centersEqual]
      exact
        retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
          _ _ _ firstSlot secondSlot directionsLe slotsLt
    · change
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterLocalRouteAt
            (retainedDirectSourceFanCenterAt first.kind first.index)
            (retainedDirectSourcePrefixChoiceAt
              first.kind first.index).direction firstSlot)
          (retainedTerminalFanFigure7SpokeAt
            (retainedDirectSourceFanCenterAt second.kind second.index)
            secondSlot)
      rw [← centersEqual]
      exact
        retainedTerminalFanOuterLocalRouteAt_strictlyAvoid_laterFigure7SpokeAt
          _ _ firstSlot secondSlot slotsLt
    · change
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanFigure7SpokeAt
            (retainedDirectSourceFanCenterAt first.kind first.index)
            firstSlot)
          (retainedTerminalFanOuterLocalRouteAt
            (retainedDirectSourceFanCenterAt second.kind second.index)
            (retainedDirectSourcePrefixChoiceAt
              second.kind second.index).direction secondSlot)
      rw [← centersEqual]
      exact
        retainedTerminalFanFigure7SpokeAt_strictlyAvoid_laterOuterLocalRouteAt
          _ _ firstSlot secondSlot slotsLt
    · change
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanFigure7SpokeAt
            (retainedDirectSourceFanCenterAt first.kind first.index)
            firstSlot)
          (retainedTerminalFanFigure7SpokeAt
            (retainedDirectSourceFanCenterAt second.kind second.index)
            secondSlot)
      rw [← centersEqual]
      exact
        retainedTerminalFanFigure7SpokesAt_strictlyAvoid
          _ firstSlot secondSlot slotsLt

/-- Equal target endpoints of two origin-zero atlas choices give the same
fully refined fan center. -/
theorem retainedDirectSourceLocalChoices_fanCenters_eq_of_sourceFinish_eq
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex :
      Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex :
      Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (finishEqual :
      (retainedDirectSourceLocalChoice
          firstKind firstIndex).sourceSegment.finish =
      (retainedDirectSourceLocalChoice
          secondKind secondIndex).sourceSegment.finish) :
    retainedDirectSourceFanCenterAt firstKind firstIndex =
      retainedDirectSourceFanCenterAt secondKind secondIndex := by
  have localFinishEqual :
      (retainedDirectSourceLocalRouteAt
          firstKind firstIndex).getLastD (0, 0) =
        (retainedDirectSourceLocalRouteAt
          secondKind secondIndex).getLastD (0, 0) := by
    simpa [RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceLocalChoice, Cell.add] using finishEqual
  have firstScaled :
      (scalePolyline (4 : Int)
        (retainedDirectSourceLocalRouteAt
          firstKind firstIndex)).getLastD (0, 0) =
        Cell.scale 4
          ((retainedDirectSourceLocalRouteAt
            firstKind firstIndex).getLastD (0, 0)) := by
    simpa using
      scalePolyline_getLastD 4
        (retainedDirectSourceLocalRouteAt firstKind firstIndex)
  have secondScaled :
      (scalePolyline (4 : Int)
        (retainedDirectSourceLocalRouteAt
          secondKind secondIndex)).getLastD (0, 0) =
        Cell.scale 4
          ((retainedDirectSourceLocalRouteAt
            secondKind secondIndex).getLastD (0, 0)) := by
    simpa using
      scalePolyline_getLastD 4
        (retainedDirectSourceLocalRouteAt secondKind secondIndex)
  unfold retainedDirectSourceFanCenterAt
  rw [firstScaled, secondScaled, localFinishEqual]

/-- Pairwise separation of the five route pieces assembles into separation
of the two complete local Figure 7 routes. -/
theorem
    retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_components
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (componentAvoid :
      ∀ firstComponent secondComponent,
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedDirectSourceSameTargetComponentRoute
            second secondSlot secondComponent)) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint
        (retainedDirectSourceFanCompleteRouteAt
          first.kind first.index firstSlot)
        (retainedDirectSourceFigure7SpokeAt
          first.kind first.index firstSlot))
      (joinAtEndpoint
        (retainedDirectSourceFanCompleteRouteAt
          second.kind second.index secondSlot)
        (retainedDirectSourceFigure7SpokeAt
          second.kind second.index secondSlot)) := by
  have componentAvoidSecondFigure7
      (firstComponent : RetainedDirectSourceSameTargetComponent) :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceSameTargetComponentRoute
          first firstSlot firstComponent)
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            second.kind second.index secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            second.kind second.index secondSlot)) := by
    have avoidEscape :=
      componentAvoid firstComponent .escape
    have avoidLane :=
      componentAvoid firstComponent .laneShift
    have avoidRemaining :=
      componentAvoid firstComponent .remainingRay
    have avoidLocal :=
      componentAvoid firstComponent .localAdapter
    have avoidSpoke :=
      componentAvoid firstComponent .figure7Spoke
    have avoidShiftedTail :
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt
              second.kind second.index)
            (retainedDirectSourceFanTerminalAt
              second.kind second.index)
            secondSlot) := by
      unfold retainedTerminalFanOuterEscapedShiftedTail
      exact avoidLane.join_right avoidRemaining
        (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
          (retainedTerminalFanOuterSourceEscapePoint
            (retainedDirectSourceFanCenterAt
              second.kind second.index)
            (retainedDirectSourceFanTerminalAt
              second.kind second.index)
            secondSlot)
          (retainedDirectSourceFanTerminalAt
            second.kind second.index).1
          secondSlot)
        (RetainedRay.rasterize_head?
          (retainedTerminalFanOuterEscapedRemainingRay
            (retainedDirectSourceFanTerminalAt
              second.kind second.index))
          (Cell.add
            (retainedTerminalFanOuterSourceEscapePoint
              (retainedDirectSourceFanCenterAt
                second.kind second.index)
              (retainedDirectSourceFanTerminalAt
                second.kind second.index)
              secondSlot)
            (retainedTerminalFanOuterLaneOffset
              (retainedDirectSourceFanTerminalAt
                second.kind second.index).1
              secondSlot)))
    have avoidRadial :
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedTerminalFanOuterCoordinatedEscapedRadialRoute
            (retainedDirectSourceFanCenterAt
              second.kind second.index)
            (retainedDirectSourceFanTerminalAt
              second.kind second.index)
            secondSlot
            (retainedDirectSourceFanEscapeAt
              second.kind second.index secondSlot)) := by
      unfold retainedTerminalFanOuterCoordinatedEscapedRadialRoute
      exact avoidEscape.join_right avoidShiftedTail
        (retainedDirectSourceFanEscapeAt
          second.kind second.index secondSlot).last_eq
        (retainedTerminalFanOuterEscapedShiftedTail_head?
          (retainedDirectSourceFanCenterAt
            second.kind second.index)
          (retainedDirectSourceFanTerminalAt
            second.kind second.index)
          secondSlot)
    have avoidComplete :
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedDirectSourceFanCompleteRouteAt
            second.kind second.index secondSlot) := by
      unfold retainedDirectSourceFanCompleteRouteAt
        retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
      exact avoidRadial.join_right avoidLocal
        (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast?
          (retainedDirectSourceFanCenterAt
            second.kind second.index)
          (retainedDirectSourceFanTerminalAt
            second.kind second.index)
          secondSlot
          (retainedDirectSourceFanEscapeAt
            second.kind second.index secondSlot)
          (retainedDirectSourceFanTerminalAt_length_positive
            second.kind second.index)
          (retainedDirectSourceFanTerminalAt_escape_fits
            second.kind second.index))
        (retainedTerminalFanOuterLocalRouteAt_head?
          (retainedDirectSourceFanCenterAt
            second.kind second.index)
          (retainedDirectSourceFanTerminalAt
            second.kind second.index).1
          secondSlot)
    exact avoidComplete.join_right avoidSpoke
      (retainedDirectSourceFanCompleteRouteAt_getLast?
        second.kind second.index secondSlot)
      (retainedDirectSourceFigure7SpokeAt_head?
        second.kind second.index secondSlot)
  have escapeAvoidFull :=
    componentAvoidSecondFigure7 .escape
  have laneAvoidFull :=
    componentAvoidSecondFigure7 .laneShift
  have remainingAvoidFull :=
    componentAvoidSecondFigure7 .remainingRay
  have localAvoidFull :=
    componentAvoidSecondFigure7 .localAdapter
  have spokeAvoidFull :=
    componentAvoidSecondFigure7 .figure7Spoke
  have shiftedTailAvoidFull :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedShiftedTail
          (retainedDirectSourceFanCenterAt first.kind first.index)
          (retainedDirectSourceFanTerminalAt first.kind first.index)
          firstSlot)
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            second.kind second.index secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            second.kind second.index secondSlot)) := by
    unfold retainedTerminalFanOuterEscapedShiftedTail
    exact laneAvoidFull.join_left remainingAvoidFull
      (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
        (retainedTerminalFanOuterSourceEscapePoint
          (retainedDirectSourceFanCenterAt first.kind first.index)
          (retainedDirectSourceFanTerminalAt first.kind first.index)
          firstSlot)
        (retainedDirectSourceFanTerminalAt
          first.kind first.index).1
        firstSlot)
      (RetainedRay.rasterize_head?
        (retainedTerminalFanOuterEscapedRemainingRay
          (retainedDirectSourceFanTerminalAt first.kind first.index))
        (Cell.add
          (retainedTerminalFanOuterSourceEscapePoint
            (retainedDirectSourceFanCenterAt first.kind first.index)
            (retainedDirectSourceFanTerminalAt first.kind first.index)
            firstSlot)
          (retainedTerminalFanOuterLaneOffset
            (retainedDirectSourceFanTerminalAt
              first.kind first.index).1
            firstSlot)))
  have radialAvoidFull :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedRadialRoute
          (retainedDirectSourceFanCenterAt first.kind first.index)
          (retainedDirectSourceFanTerminalAt first.kind first.index)
          firstSlot
          (retainedDirectSourceFanEscapeAt
            first.kind first.index firstSlot))
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            second.kind second.index secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            second.kind second.index secondSlot)) := by
    unfold retainedTerminalFanOuterCoordinatedEscapedRadialRoute
    exact escapeAvoidFull.join_left shiftedTailAvoidFull
      (retainedDirectSourceFanEscapeAt
        first.kind first.index firstSlot).last_eq
      (retainedTerminalFanOuterEscapedShiftedTail_head?
        (retainedDirectSourceFanCenterAt first.kind first.index)
        (retainedDirectSourceFanTerminalAt first.kind first.index)
        firstSlot)
  have completeAvoidFull :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          first.kind first.index firstSlot)
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            second.kind second.index secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            second.kind second.index secondSlot)) := by
    unfold retainedDirectSourceFanCompleteRouteAt
      retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
    exact radialAvoidFull.join_left localAvoidFull
      (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast?
        (retainedDirectSourceFanCenterAt first.kind first.index)
        (retainedDirectSourceFanTerminalAt first.kind first.index)
        firstSlot
        (retainedDirectSourceFanEscapeAt
          first.kind first.index firstSlot)
        (retainedDirectSourceFanTerminalAt_length_positive
          first.kind first.index)
        (retainedDirectSourceFanTerminalAt_escape_fits
          first.kind first.index))
      (retainedTerminalFanOuterLocalRouteAt_head?
        (retainedDirectSourceFanCenterAt first.kind first.index)
        (retainedDirectSourceFanTerminalAt first.kind first.index).1
        firstSlot)
  exact completeAvoidFull.join_left spokeAvoidFull
    (retainedDirectSourceFanCompleteRouteAt_getLast?
      first.kind first.index firstSlot)
    (retainedDirectSourceFigure7SpokeAt_head?
      first.kind first.index firstSlot)

/-- Every atlas-handled component pair of an ordered same-target crossover
pair has a linear separator. -/
theorem
    retainedDirectSourceCrossoverCrossClauseSameTarget_componentsLinearlySeparated :
    ∀ (firstClauseIndex secondClauseIndex : Fin 26)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover secondClauseIndex)).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstClauseIndex ≠ secondClauseIndex →
      let first :=
        retainedDirectSourceLocalChoice
          (.crossover firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish →
      firstSlot.val < secondSlot.val →
      (retainedDirectSourcePrefixChoiceAt
          first.kind first.index).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          second.kind second.index).direction.angularRank →
      ∀ firstComponent secondComponent,
        retainedDirectSourceSameTargetUsesAtlasCertificate
            firstComponent secondComponent = true →
          retainedDirectSourceSameTargetComponentsLinearlySeparated
            first second firstSlot secondSlot
            firstComponent secondComponent := by
  native_decide

/-- Every atlas-handled component pair of an ordered same-target duplicator
pair has a linear separator. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseSameTarget_componentsLinearlySeparated :
    ∀ (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
      (firstClauseIndex secondClauseIndex : Fin 2)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator firstArm firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator secondArm secondClauseIndex)).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      (firstArm, firstClauseIndex) ≠
          (secondArm, secondClauseIndex) →
      let first :=
        retainedDirectSourceLocalChoice
          (.duplicator firstArm firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex) secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish →
      firstSlot.val < secondSlot.val →
      (retainedDirectSourcePrefixChoiceAt
          first.kind first.index).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          second.kind second.index).direction.angularRank →
      ∀ firstComponent secondComponent,
        retainedDirectSourceSameTargetUsesAtlasCertificate
            firstComponent secondComponent = true →
          retainedDirectSourceSameTargetComponentsLinearlySeparated
            first second firstSlot secondSlot
            firstComponent secondComponent := by
  native_decide

/-- Ordered different crossover clauses converging on one target have
strictly separated complete Figure 7 routes. -/
theorem
    retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid_ordered
    (firstClauseIndex secondClauseIndex : Fin 26)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent : firstClauseIndex ≠ secondClauseIndex)
    (finishEqual :
      let first :=
        retainedDirectSourceLocalChoice
          (.crossover firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsLe :
      (retainedDirectSourcePrefixChoiceAt
          (.crossover firstClauseIndex) firstIndex).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          (.crossover secondClauseIndex) secondIndex).direction.angularRank) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.crossover secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice
      (.crossover firstClauseIndex) firstIndex
  let second :=
    retainedDirectSourceLocalChoice
      (.crossover secondClauseIndex) secondIndex
  have atlasCertificate :=
    retainedDirectSourceCrossoverCrossClauseSameTarget_componentsLinearlySeparated
      firstClauseIndex secondClauseIndex firstIndex secondIndex
      firstSlot secondSlot clausesDifferent finishEqual
      slotsLt directionsLe
  have centersEqual :=
    retainedDirectSourceLocalChoices_fanCenters_eq_of_sourceFinish_eq
      (.crossover firstClauseIndex)
      (.crossover secondClauseIndex)
      firstIndex secondIndex finishEqual
  have componentAvoid :
      ∀ firstComponent secondComponent,
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedDirectSourceSameTargetComponentRoute
            second secondSlot secondComponent) :=
    retainedDirectSourceSameTargetComponentRoutes_strictlyAvoid
      first second firstSlot secondSlot slotsLt directionsLe
      centersEqual atlasCertificate
  have raw :=
    retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_components
      first second firstSlot secondSlot componentAvoid
  simpa [first, second,
    RetainedDirectSourceRouteChoice.completeFigure7Route,
    RetainedDirectSourceRouteChoice.completeRoute,
    RetainedDirectSourceRouteChoice.figure7Spoke,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourceLocalChoice] using raw

/-- Ordered different duplicator clauses converging on one target have
strictly separated complete Figure 7 routes. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid_ordered
    (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
    (firstClauseIndex secondClauseIndex : Fin 2)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator firstArm firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator secondArm secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent :
      (firstArm, firstClauseIndex) ≠
        (secondArm, secondClauseIndex))
    (finishEqual :
      let first :=
        retainedDirectSourceLocalChoice
          (.duplicator firstArm firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex) secondIndex
      first.sourceSegment.finish = second.sourceSegment.finish)
    (slotsLt : firstSlot.val < secondSlot.val)
    (directionsLe :
      (retainedDirectSourcePrefixChoiceAt
          (.duplicator firstArm firstClauseIndex)
          firstIndex).direction.angularRank ≤
        (retainedDirectSourcePrefixChoiceAt
          (.duplicator secondArm secondClauseIndex)
          secondIndex).direction.angularRank) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.duplicator secondArm secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice
      (.duplicator firstArm firstClauseIndex) firstIndex
  let second :=
    retainedDirectSourceLocalChoice
      (.duplicator secondArm secondClauseIndex) secondIndex
  have atlasCertificate :=
    retainedDirectSourceDuplicatorCrossClauseSameTarget_componentsLinearlySeparated
      firstArm secondArm firstClauseIndex secondClauseIndex
      firstIndex secondIndex firstSlot secondSlot
      clausesDifferent finishEqual slotsLt directionsLe
  have centersEqual :=
    retainedDirectSourceLocalChoices_fanCenters_eq_of_sourceFinish_eq
      (.duplicator firstArm firstClauseIndex)
      (.duplicator secondArm secondClauseIndex)
      firstIndex secondIndex finishEqual
  have componentAvoid :
      ∀ firstComponent secondComponent,
        RoutesStrictlyAvoidEachOther
          (retainedDirectSourceSameTargetComponentRoute
            first firstSlot firstComponent)
          (retainedDirectSourceSameTargetComponentRoute
            second secondSlot secondComponent) :=
    retainedDirectSourceSameTargetComponentRoutes_strictlyAvoid
      first second firstSlot secondSlot slotsLt directionsLe
      centersEqual atlasCertificate
  have raw :=
    retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_components
      first second firstSlot secondSlot componentAvoid
  simpa [first, second,
    RetainedDirectSourceRouteChoice.completeFigure7Route,
    RetainedDirectSourceRouteChoice.completeRoute,
    RetainedDirectSourceRouteChoice.figure7Spoke,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourceLocalChoice] using raw

/-- Angular-order-compatible crossover routes from different clauses may be
presented in either slot order. -/
theorem
    retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid
    (firstClauseIndex secondClauseIndex : Fin 26)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent : firstClauseIndex ≠ secondClauseIndex)
    (finishEqual :
      (retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex).sourceSegment.finish =
        (retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex).sourceSegment.finish)
    (angularOrder :
      (retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.AngularOrderCompatible
            (retainedDirectSourceLocalChoice
              (.crossover secondClauseIndex) secondIndex)
            firstSlot secondSlot) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.crossover secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  unfold RetainedDirectSourceRouteChoice.AngularOrderCompatible
    at angularOrder
  rcases angularOrder with
      ⟨slotsLt, directionsLe⟩ |
      ⟨slotsLt, directionsLe⟩
  · exact
      retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid_ordered
        firstClauseIndex secondClauseIndex firstIndex secondIndex
        firstSlot secondSlot clausesDifferent finishEqual
        slotsLt directionsLe
  · exact
      (retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid_ordered
        secondClauseIndex firstClauseIndex secondIndex firstIndex
        secondSlot firstSlot clausesDifferent.symm finishEqual.symm
        slotsLt directionsLe).symm

/-- Angular-order-compatible duplicator routes from different local clauses
may be presented in either slot order. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid
    (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
    (firstClauseIndex secondClauseIndex : Fin 2)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator firstArm firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator secondArm secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent :
      (firstArm, firstClauseIndex) ≠
        (secondArm, secondClauseIndex))
    (finishEqual :
      (retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex)
          firstIndex).sourceSegment.finish =
        (retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex)
          secondIndex).sourceSegment.finish)
    (angularOrder :
      (retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.AngularOrderCompatible
            (retainedDirectSourceLocalChoice
              (.duplicator secondArm secondClauseIndex) secondIndex)
            firstSlot secondSlot) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.duplicator secondArm secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  unfold RetainedDirectSourceRouteChoice.AngularOrderCompatible
    at angularOrder
  rcases angularOrder with
      ⟨slotsLt, directionsLe⟩ |
      ⟨slotsLt, directionsLe⟩
  · exact
      retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid_ordered
        firstArm secondArm firstClauseIndex secondClauseIndex
        firstIndex secondIndex firstSlot secondSlot
        clausesDifferent finishEqual slotsLt directionsLe
  · exact
      (retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid_ordered
        secondArm firstArm secondClauseIndex firstClauseIndex
        secondIndex firstIndex secondSlot firstSlot
        clausesDifferent.symm finishEqual.symm
        slotsLt directionsLe).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes

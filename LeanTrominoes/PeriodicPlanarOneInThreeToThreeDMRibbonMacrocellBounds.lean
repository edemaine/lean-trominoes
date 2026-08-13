/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocells

/-!
# Bounding boxes for ribbon macrocells

Every half-edge ribbon tile lies in the closed `128 × 128` block based at
its refined source lattice point and centered at local coordinate
`(64, 64)`.  Consequently tiles whose source centers differ by at least two
in either lattice coordinate cannot meet at all.  An exhaustive certificate
covers the eight remaining nonzero offsets, so any legal tiles with distinct
source centers satisfy complete continuous route separation.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- A refined point lies in the closed ribbon block owned by one source
lattice point. -/
def InRibbonMacrocell (center point : Cell) : Prop :=
  (ribbonMacrocellOrigin center).1 ≤ point.1 ∧
    point.1 ≤
      (ribbonMacrocellOrigin center).1 +
        standardThreeStrandLayout.factor ∧
    (ribbonMacrocellOrigin center).2 ≤ point.2 ∧
    point.2 ≤
      (ribbonMacrocellOrigin center).2 +
        standardThreeStrandLayout.factor

instance (center point : Cell) :
    Decidable (InRibbonMacrocell center point) := by
  unfold InRibbonMacrocell
  infer_instance

/-- The local version of the closed ribbon-macrocell bound. -/
def InStandardRibbonMacrocell (point : Cell) : Prop :=
  0 ≤ point.1 ∧
    point.1 ≤ standardThreeStrandLayout.factor ∧
    0 ≤ point.2 ∧
    point.2 ≤ standardThreeStrandLayout.factor

instance (point : Cell) :
    Decidable (InStandardRibbonMacrocell point) := by
  unfold InStandardRibbonMacrocell
  infer_instance

/-- Every listed point of every standard ribbon tile lies in its closed
standard macrocell. -/
theorem standardRibbonMacrocellRoute_points_bounded
    (incoming outgoing : AxisDirection)
    (color : Gadget.WireColor) :
    ∀ point ∈
        standardRibbonMacrocellRoute incoming outgoing color,
      InStandardRibbonMacrocell point := by
  cases incoming <;> cases outgoing <;> cases color <;>
    simp [standardRibbonMacrocellRoute,
      standardRibbonMacrocellEntry,
      standardRibbonMacrocellExit,
      standardRibbonMacrocellCenter,
      standardRibbonMacrocellHalfSpan,
      standardThreeStrandLayout,
      standardRibbonLaneDistance,
      AxisDirection.step, AxisDirection.rightNormal,
      AxisDirection.opposite, AxisDirection.TurnsRight,
      InStandardRibbonMacrocell, Cell.add, Cell.scale]

/-- Translating a locally bounded point by a macrocell origin gives the
corresponding global bound. -/
theorem inRibbonMacrocell_add_origin
    {center localPoint : Cell}
    (bounded : InStandardRibbonMacrocell localPoint) :
    InRibbonMacrocell center
      (Cell.add (ribbonMacrocellOrigin center) localPoint) := by
  rcases center with ⟨centerX, centerY⟩
  rcases localPoint with ⟨localX, localY⟩
  simp only [InStandardRibbonMacrocell,
    standardThreeStrandLayout] at bounded
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    standardThreeStrandLayout,
    Cell.add, Cell.scale]
  omega

/-- Every listed point of a translated ribbon tile lies in its centered
closed macrocell. -/
theorem ribbonMacrocellRoute_points_bounded
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : Gadget.WireColor) :
    ∀ point ∈
        ribbonMacrocellRoute center incoming outgoing color,
      InRibbonMacrocell center point := by
  intro point pointMember
  unfold ribbonMacrocellRoute at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact inRibbonMacrocell_add_origin
    (standardRibbonMacrocellRoute_points_bounded
      incoming outgoing color localPoint localMember)

/-- Adding a source center translates the corresponding relative ribbon
tile by the refined origin of that center. -/
theorem ribbonMacrocellRoute_add_center
    (center relative : Cell)
    (incoming outgoing : AxisDirection)
    (color : Gadget.WireColor) :
    ribbonMacrocellRoute (Cell.add center relative)
        incoming outgoing color =
      (ribbonMacrocellRoute relative
        incoming outgoing color).map
          (Cell.add (ribbonMacrocellOrigin center)) := by
  unfold ribbonMacrocellRoute
  rw [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases center with ⟨centerX, centerY⟩
  rcases relative with ⟨relativeX, relativeY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [ribbonMacrocellOrigin, standardThreeStrandLayout,
    Cell.add, Cell.scale]
  constructor <;> ring

/-- Two source centers are non-neighboring when they differ by at least two
lattice units in one coordinate. -/
def RibbonMacrocellCentersFar
    (first second : Cell) : Prop :=
  first.1 + 2 ≤ second.1 ∨ second.1 + 2 ≤ first.1 ∨
    first.2 + 2 ≤ second.2 ∨ second.2 + 2 ≤ first.2

instance (first second : Cell) :
    Decidable (RibbonMacrocellCentersFar first second) := by
  unfold RibbonMacrocellCentersFar
  infer_instance

/-- Being separated by at least two lattice units is symmetric. -/
theorem RibbonMacrocellCentersFar.symm
    {first second : Cell}
    (far : RibbonMacrocellCentersFar first second) :
    RibbonMacrocellCentersFar second first := by
  rcases far with horizontalForward | horizontalBackward |
      verticalForward | verticalBackward
  · exact Or.inr (Or.inl horizontalForward)
  · exact Or.inl horizontalBackward
  · exact Or.inr (Or.inr (Or.inr verticalForward))
  · exact Or.inr (Or.inr (Or.inl verticalBackward))

/-- A nonzero source offset in the surrounding `3 × 3` block. -/
def RibbonMacrocellOffsetAdjacent (offset : Cell) : Prop :=
  -1 ≤ offset.1 ∧ offset.1 ≤ 1 ∧
    -1 ≤ offset.2 ∧ offset.2 ≤ 1 ∧
    offset ≠ (0, 0)

instance (offset : Cell) :
    Decidable (RibbonMacrocellOffsetAdjacent offset) := by
  unfold RibbonMacrocellOffsetAdjacent
  infer_instance

/-- Two distinct source centers in the same surrounding `3 × 3` block. -/
def RibbonMacrocellCentersAdjacent
    (first second : Cell) : Prop :=
  RibbonMacrocellOffsetAdjacent (Cell.sub second first)

instance (first second : Cell) :
    Decidable (RibbonMacrocellCentersAdjacent first second) := by
  unfold RibbonMacrocellCentersAdjacent
  infer_instance

/-- Any two source centers are equal, far enough for the bounding-box
argument, or one of the eight adjacent pairs. -/
theorem ribbonMacrocellCenters_eq_or_far_or_adjacent
    (first second : Cell) :
    first = second ∨ RibbonMacrocellCentersFar first second ∨
      RibbonMacrocellCentersAdjacent first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  by_cases equal :
      (firstX, firstY) = (secondX, secondY)
  · exact Or.inl equal
  · right
    by_cases far :
        RibbonMacrocellCentersFar
          (firstX, firstY) (secondX, secondY)
    · exact Or.inl far
    · right
      unfold RibbonMacrocellCentersAdjacent
        RibbonMacrocellOffsetAdjacent
      simp only [Cell.sub]
      refine ⟨by
        unfold RibbonMacrocellCentersFar at far
        omega, by
        unfold RibbonMacrocellCentersFar at far
        omega, by
        unfold RibbonMacrocellCentersFar at far
        omega, by
        unfold RibbonMacrocellCentersFar at far
        omega, ?_⟩
      intro zero
      apply equal
      simp only [Prod.mk.injEq] at zero ⊢
      omega

/-- Closed ribbon macrocells with non-neighboring centers have no common
point. -/
theorem ne_of_inRibbonMacrocells_of_centersFar
    {firstCenter secondCenter firstPoint secondPoint : Cell}
    (firstBounded :
      InRibbonMacrocell firstCenter firstPoint)
    (secondBounded :
      InRibbonMacrocell secondCenter secondPoint)
    (far :
      RibbonMacrocellCentersFar firstCenter secondCenter) :
    firstPoint ≠ secondPoint := by
  rcases firstCenter with ⟨firstCenterX, firstCenterY⟩
  rcases secondCenter with ⟨secondCenterX, secondCenterY⟩
  rcases firstPoint with ⟨firstX, firstY⟩
  rcases secondPoint with ⟨secondX, secondY⟩
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    standardThreeStrandLayout,
    Cell.scale] at firstBounded secondBounded
  simp only [RibbonMacrocellCentersFar] at far
  intro equal
  simp only [Prod.mk.injEq] at equal
  rcases far with far | far | far | far <;> omega

/-- A point in one ribbon macrocell cannot lie in the relative interior of
a segment whose endpoints lie in a non-neighboring macrocell. -/
theorem not_interiorContains_of_inRibbonMacrocells_of_centersFar
    {pointCenter segmentCenter point : Cell}
    {segment : GridSegment}
    (pointBounded :
      InRibbonMacrocell pointCenter point)
    (startBounded :
      InRibbonMacrocell segmentCenter segment.start)
    (finishBounded :
      InRibbonMacrocell segmentCenter segment.finish)
    (far :
      RibbonMacrocellCentersFar pointCenter segmentCenter) :
    ¬segment.InteriorContains point := by
  rcases pointCenter with ⟨pointCenterX, pointCenterY⟩
  rcases segmentCenter with ⟨segmentCenterX, segmentCenterY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    standardThreeStrandLayout,
    Cell.scale] at pointBounded startBounded finishBounded
  simp only [RibbonMacrocellCentersFar] at far
  simp only [GridSegment.InteriorContains,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.StrictlyBetween]
  rcases far with far | far | far | far <;> omega

/-- Segment interiors contained in non-neighboring ribbon macrocells are
disjoint. -/
theorem not_interiorsMeet_of_inRibbonMacrocells_of_centersFar
    {firstCenter secondCenter : Cell}
    {first second : GridSegment}
    (firstStart :
      InRibbonMacrocell firstCenter first.start)
    (firstFinish :
      InRibbonMacrocell firstCenter first.finish)
    (secondStart :
      InRibbonMacrocell secondCenter second.start)
    (secondFinish :
      InRibbonMacrocell secondCenter second.finish)
    (far :
      RibbonMacrocellCentersFar firstCenter secondCenter) :
    ¬GridSegment.InteriorsMeet first second := by
  rcases firstCenter with ⟨firstCenterX, firstCenterY⟩
  rcases secondCenter with ⟨secondCenterX, secondCenterY⟩
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    standardThreeStrandLayout,
    Cell.scale] at firstStart firstFinish secondStart secondFinish
  simp only [RibbonMacrocellCentersFar] at far
  simp only [GridSegment.InteriorsMeet,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.OpenIntervalsOverlap,
    GridSegment.StrictlyBetween]
  rcases far with far | far | far | far <;>
    simp_all [min_def, max_def] <;>
    omega

/-- Any two finite routes contained in non-neighboring ribbon macrocells
satisfy complete contact-free separation. -/
theorem routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
    {firstCenter secondCenter : Cell}
    {first second : List Cell}
    (firstBounded :
      ∀ point ∈ first,
        InRibbonMacrocell firstCenter point)
    (secondBounded :
      ∀ point ∈ second,
        InRibbonMacrocell secondCenter point)
    (far :
      RibbonMacrocellCentersFar firstCenter secondCenter) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      first second := by
  unfold
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondMember
    exact
      not_interiorsMeet_of_inRibbonMacrocells_of_centersFar
        (firstBounded _ firstEndpoints.1)
        (firstBounded _ firstEndpoints.2)
        (secondBounded _ secondEndpoints.1)
        (secondBounded _ secondEndpoints.2)
        far
  · intro firstPoint firstPointMember
      secondSegment secondSegmentMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondSegmentMember
    exact
      not_interiorContains_of_inRibbonMacrocells_of_centersFar
        (firstBounded _ firstPointMember)
        (secondBounded _ secondEndpoints.1)
        (secondBounded _ secondEndpoints.2)
        far
  · intro secondPoint secondPointMember
      firstSegment firstSegmentMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstSegmentMember
    exact
      not_interiorContains_of_inRibbonMacrocells_of_centersFar
        (secondBounded _ secondPointMember)
        (firstBounded _ firstEndpoints.1)
        (firstBounded _ firstEndpoints.2)
        far.symm
  · intro firstPoint firstPointMember
      secondPoint secondPointMember
    exact
      ne_of_inRibbonMacrocells_of_centersFar
        (firstBounded _ firstPointMember)
        (secondBounded _ secondPointMember)
        far

/-- Legal ribbon tiles in far source macrocells satisfy the complete
continuous route-separation predicate. -/
theorem farRibbonMacrocellRoutes_avoidEachOther
    {firstCenter secondCenter : Cell}
    (far :
      RibbonMacrocellCentersFar firstCenter secondCenter)
    (firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute secondCenter
        secondIncoming secondOutgoing secondColor) := by
  exact
    (routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
      (fun point member =>
        ribbonMacrocellRoute_points_bounded
          firstCenter firstIncoming firstOutgoing firstColor
          point member)
      (fun point member =>
        ribbonMacrocellRoute_points_bounded
          secondCenter secondIncoming secondOutgoing secondColor
          point member)
      far).toRoutesAvoidEachOther

/-- The eight nonzero offsets in the surrounding `3 × 3` block. -/
private def adjacentRibbonMacrocellOffsets : List Cell :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1),
    (0, 1), (1, -1), (1, 0), (1, 1)]

private theorem mem_adjacentRibbonMacrocellOffsets_iff
    (offset : Cell) :
    offset ∈ adjacentRibbonMacrocellOffsets ↔
      RibbonMacrocellOffsetAdjacent offset := by
  rcases offset with ⟨offsetX, offsetY⟩
  simp [adjacentRibbonMacrocellOffsets,
    RibbonMacrocellOffsetAdjacent]
  omega

/-- A genuine cardinal step is one of the eight adjacent offsets. -/
theorem ribbonMacrocellOffsetAdjacent_step
    {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    RibbonMacrocellOffsetAdjacent direction.step := by
  cases direction <;>
    simp_all [AxisDirection.IsGenuine,
      AxisDirection.step, RibbonMacrocellOffsetAdjacent]

/-- The twelve genuine, nonreversing incoming/outgoing direction pairs. -/
private def legalRibbonTurns :
    List (AxisDirection × AxisDirection) :=
  [(.east, .east), (.east, .north), (.east, .south),
    (.north, .east), (.north, .north), (.north, .west),
    (.west, .north), (.west, .west), (.west, .south),
    (.south, .east), (.south, .west), (.south, .south)]

private theorem mem_legalRibbonTurns_iff
    (incoming outgoing : AxisDirection) :
    (incoming, outgoing) ∈ legalRibbonTurns ↔
      incoming.IsGenuine ∧ outgoing.IsGenuine ∧
        outgoing ≠ incoming.opposite := by
  cases incoming <;> cases outgoing <;>
    decide

/-- The three ribbon colors, used to package finite geometry checks. -/
private def ribbonWireColors : List Gadget.WireColor :=
  [.red, .green, .blue]

private theorem mem_ribbonWireColors
    (color : Gadget.WireColor) :
    color ∈ ribbonWireColors := by
  cases color <;>
    simp [ribbonWireColors]

/-- One executable check of all `8 · 12² · 3² = 10,368` legal pairs of
tiles in distinct adjacent macrocells. -/
private def allOriginAdjacentRibbonMacrocellRoutesAvoid : Bool :=
  adjacentRibbonMacrocellOffsets.all fun offset =>
    legalRibbonTurns.all fun firstTurn =>
      legalRibbonTurns.all fun secondTurn =>
        ribbonWireColors.all fun firstColor =>
          ribbonWireColors.all fun secondColor =>
            decide
              (PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
                (ribbonMacrocellRoute (0, 0)
                  firstTurn.1 firstTurn.2 firstColor)
                (ribbonMacrocellRoute offset
                  secondTurn.1 secondTurn.2 secondColor))

private theorem allOriginAdjacentRibbonMacrocellRoutesAvoid_eq_true :
    allOriginAdjacentRibbonMacrocellRoutesAvoid = true := by
  native_decide

/-- At the origin, every pair of legal tiles in distinct adjacent source
macrocells is continuously compatible. -/
theorem originAdjacentRibbonMacrocellRoutes_avoidEachOther
    {offset : Cell}
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute (0, 0)
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute offset
        secondIncoming secondOutgoing secondColor) := by
  have checked :=
    allOriginAdjacentRibbonMacrocellRoutesAvoid_eq_true
  simp only [allOriginAdjacentRibbonMacrocellRoutesAvoid,
    List.all_eq_true, decide_eq_true_eq] at checked
  exact checked offset
    ((mem_adjacentRibbonMacrocellOffsets_iff offset).2
      offsetAdjacent)
    (firstIncoming, firstOutgoing)
    ((mem_legalRibbonTurns_iff
      firstIncoming firstOutgoing).2
        ⟨firstIncomingGenuine, firstOutgoingGenuine,
          firstNoReverse⟩)
    (secondIncoming, secondOutgoing)
    ((mem_legalRibbonTurns_iff
      secondIncoming secondOutgoing).2
        ⟨secondIncomingGenuine, secondOutgoingGenuine,
          secondNoReverse⟩)
    firstColor (mem_ribbonWireColors firstColor)
    secondColor (mem_ribbonWireColors secondColor)

/-- Every pair of legal tiles in distinct adjacent source macrocells is
continuously compatible, at any source center. -/
theorem adjacentRibbonMacrocellRoutes_avoidEachOther
    (center : Cell) {offset : Cell}
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute center
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute
        (Cell.add center offset)
        secondIncoming secondOutgoing secondColor) := by
  have originAvoids :=
    originAdjacentRibbonMacrocellRoutes_avoidEachOther
      offsetAdjacent
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor
  have translated :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_translate
      originAvoids (ribbonMacrocellOrigin center)
  have firstTranslation :
      ribbonMacrocellRoute center
          firstIncoming firstOutgoing firstColor =
        (ribbonMacrocellRoute (0, 0)
          firstIncoming firstOutgoing firstColor).map
            (Cell.add (ribbonMacrocellOrigin center)) := by
    simpa [Cell.add] using
      ribbonMacrocellRoute_add_center center (0, 0)
        firstIncoming firstOutgoing firstColor
  rw [firstTranslation,
    ribbonMacrocellRoute_add_center center offset]
  exact translated

/-- The adjacent-macrocell certificate expressed directly in terms of two
source centers. -/
theorem adjacentCentersRibbonMacrocellRoutes_avoidEachOther
    {firstCenter secondCenter : Cell}
    (adjacent :
      RibbonMacrocellCentersAdjacent firstCenter secondCenter)
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute secondCenter
        secondIncoming secondOutgoing secondColor) := by
  let offset := Cell.sub secondCenter firstCenter
  have secondEquation :
      secondCenter = Cell.add firstCenter offset := by
    rcases firstCenter with ⟨firstX, firstY⟩
    rcases secondCenter with ⟨secondX, secondY⟩
    simp [offset, Cell.sub, Cell.add]
  rw [secondEquation]
  exact
    adjacentRibbonMacrocellRoutes_avoidEachOther firstCenter
      (by simpa [offset, RibbonMacrocellCentersAdjacent] using
        adjacent)
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor

/-- Any two legal tiles with distinct source centers satisfy complete
continuous route separation. -/
theorem ribbonMacrocellRoutes_avoidEachOther_of_centers_ne
    {firstCenter secondCenter : Cell}
    (centersDifferent : firstCenter ≠ secondCenter)
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute secondCenter
        secondIncoming secondOutgoing secondColor) := by
  rcases
      ribbonMacrocellCenters_eq_or_far_or_adjacent
        firstCenter secondCenter with
    equal | far | adjacent
  · exact (centersDifferent equal).elim
  · exact
      farRibbonMacrocellRoutes_avoidEachOther far
        firstIncoming firstOutgoing
        secondIncoming secondOutgoing
        firstColor secondColor
  · exact
      adjacentCentersRibbonMacrocellRoutes_avoidEachOther adjacent
        firstIncomingGenuine firstOutgoingGenuine firstNoReverse
        secondIncomingGenuine secondOutgoingGenuine secondNoReverse
        firstColor secondColor

/-- At the origin, every pair of legal tiles in edge-neighboring source
macrocells is continuously compatible.  When both tiles use their common
source edge in the same direction and color, their only contact is the
intended shared endpoint. -/
theorem originNeighborRibbonMacrocellRoutes_avoidEachOther
    {direction firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (directionGenuine : direction.IsGenuine)
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute (0, 0)
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute direction.step
        secondIncoming secondOutgoing secondColor) := by
  exact
    originAdjacentRibbonMacrocellRoutes_avoidEachOther
      (ribbonMacrocellOffsetAdjacent_step directionGenuine)
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor

/-- Every pair of legal tiles in edge-neighboring source macrocells is
continuously compatible, at any source center. -/
theorem neighborRibbonMacrocellRoutes_avoidEachOther
    (center : Cell)
    {direction firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (directionGenuine : direction.IsGenuine)
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute center
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute
        (Cell.add center direction.step)
        secondIncoming secondOutgoing secondColor) := by
  exact
    adjacentRibbonMacrocellRoutes_avoidEachOther center
      (ribbonMacrocellOffsetAdjacent_step directionGenuine)
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

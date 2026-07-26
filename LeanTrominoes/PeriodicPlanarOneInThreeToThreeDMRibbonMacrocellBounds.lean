import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocells

/-!
# Bounding boxes for ribbon macrocells

Every half-edge ribbon tile lies in the closed square of half-span `64`
around its `128`-refined source lattice point.  Consequently tiles whose
source centers differ by at least two in either lattice coordinate cannot
meet at all.  This isolates the remaining global corridor-planarity proof
to equal or neighboring source macrocells.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- A refined point lies in the closed ribbon macrocell centered at one
source lattice point. -/
def InRibbonMacrocell (center point : Cell) : Prop :=
  (ribbonMacrocellOrigin center).1 -
        standardRibbonMacrocellHalfSpan ≤ point.1 ∧
    point.1 ≤
      (ribbonMacrocellOrigin center).1 +
        standardRibbonMacrocellHalfSpan ∧
    (ribbonMacrocellOrigin center).2 -
        standardRibbonMacrocellHalfSpan ≤ point.2 ∧
    point.2 ≤
      (ribbonMacrocellOrigin center).2 +
        standardRibbonMacrocellHalfSpan

instance (center point : Cell) :
    Decidable (InRibbonMacrocell center point) := by
  unfold InRibbonMacrocell
  infer_instance

/-- The local version of the closed ribbon-macrocell bound. -/
def InStandardRibbonMacrocell (point : Cell) : Prop :=
  -standardRibbonMacrocellHalfSpan ≤ point.1 ∧
    point.1 ≤ standardRibbonMacrocellHalfSpan ∧
    -standardRibbonMacrocellHalfSpan ≤ point.2 ∧
    point.2 ≤ standardRibbonMacrocellHalfSpan

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
      standardRibbonMacrocellHalfSpan,
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
    standardRibbonMacrocellHalfSpan] at bounded
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    standardThreeStrandLayout, standardRibbonMacrocellHalfSpan,
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
    standardThreeStrandLayout, standardRibbonMacrocellHalfSpan,
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
    standardThreeStrandLayout, standardRibbonMacrocellHalfSpan,
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
    standardThreeStrandLayout, standardRibbonMacrocellHalfSpan,
    Cell.scale] at firstStart firstFinish secondStart secondFinish
  simp only [RibbonMacrocellCentersFar] at far
  simp only [GridSegment.InteriorsMeet,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.OpenIntervalsOverlap,
    GridSegment.StrictlyBetween]
  rcases far with far | far | far | far <;>
    simp_all [min_def, max_def] <;>
    omega

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

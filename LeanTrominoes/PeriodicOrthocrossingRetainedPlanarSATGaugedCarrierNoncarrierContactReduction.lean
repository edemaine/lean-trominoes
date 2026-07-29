import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierPeriodicSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierAnchorGeometry

/-!
# Reducing carrier--noncarrier contact to finite-halo closure

A selected carrier source is already a neighboring raw retained link.  To
compare it with an arbitrary final noncarrier occurrence, keep that carrier
source fixed and translate the noncarrier source by the difference of their
physical shifts.  Both resulting finite routes then use the carrier's physical
shift as their common external translate.

Consequently, periodic carrier--noncarrier separation is reduced to one
geometric closure fact: if the two final segments met, the translated
noncarrier source would still belong to the retained finite halo.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A fundamental coordinate plus an integral period translate can lie in
the half-open three-cell window `[-P, 2P)` only for shifts `-1`, `0`, or
`1`. -/
theorem fundamental_translate_shift_is_neighbor
    {period base shift lifted : Int}
    (periodPositive : 0 < period)
    (basePositive : 0 < base)
    (baseUpper : base < period)
    (liftedLower : -period ≤ lifted)
    (liftedUpper : lifted < 2 * period)
    (liftedEq : lifted = base + period * shift) :
    shift = -1 ∨ shift = 0 ∨ shift = 1 := by
  have notTooLow : ¬shift ≤ -2 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -2 * period := by
      nlinarith
    omega
  have notTooHigh : ¬2 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : 2 * period ≤ period * shift := by
      nlinarith
    omega
  omega

/-- A lifted constructed-drawing vertex that still lies in the open
one-cell halo must use one of the nine neighboring lattice translations. -/
theorem liftedDrawingVertexPosition_translate_neighbor_of_inExpanded
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices)
    (translate : Cell)
    (inside :
      InExpandedDrawingSquare graph
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))) :
    IsNeighborTranslation translate := by
  let period : Int := drawingGridSize graph
  let base := (drawing graph).vertexPosition graph vertex
  let lifted :=
    Cell.add base ((drawing graph).periodTranslation translate)
  have periodPositive : 0 < period := by
    dsimp only [period]
    exact_mod_cast drawingGridSize_pos graph
  have baseBounds :=
    drawing_vertexPosition_in_fundamental_square graph vertexMember
  change
    0 < base.1 ∧ base.1 < period ∧
      0 < base.2 ∧ base.2 < period at baseBounds
  change
    -period < lifted.1 ∧ lifted.1 < 2 * period ∧
      -period < lifted.2 ∧ lifted.2 < 2 * period at inside
  have horizontalEq :
      base.1 = lifted.1 + period * (-translate.1) := by
    simp [base, lifted, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have verticalEq :
      base.2 = lifted.2 + period * (-translate.2) := by
    simp [base, lifted, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have horizontalNegativeNeighbor :=
    lane_shift_is_neighbor
      periodPositive inside.1 inside.2.1
      (le_of_lt baseBounds.1) baseBounds.2.1 horizontalEq
  have verticalNegativeNeighbor :=
    lane_shift_is_neighbor
      periodPositive inside.2.2.1 inside.2.2.2
      (le_of_lt baseBounds.2.2.1) baseBounds.2.2.2 verticalEq
  constructor <;> omega

/-- If a point of the macrocell around a lifted vertex lies in the refined
open one-cell halo, then the vertex occurrence itself is neighboring.  The
unused seven-cell macrocell margin makes the implication strict at both
period boundaries. -/
theorem liftedDrawingVertexPosition_translate_neighbor_of_macrocellPoint_inExpanded
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices)
    (translate : Cell)
    (point : Cell)
    (pointInMacrocell :
      InPlanarSATMacrocell
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))
        point)
    (pointInExpandedRefinement :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < point.1 ∧ point.1 < 2 * period ∧
        -period < point.2 ∧ point.2 < 2 * period) :
    IsNeighborTranslation translate := by
  let center :=
    Cell.add
      ((drawing graph).vertexPosition graph vertex)
      ((drawing graph).periodTranslation translate)
  let period : Int := drawingGridSize graph
  have periodPositive : 0 < period := by
    dsimp only [period]
    exact_mod_cast drawingGridSize_pos graph
  have centerBounds :
      -period ≤ center.1 ∧ center.1 < 2 * period ∧
        -period ≤ center.2 ∧ center.2 < 2 * period := by
    change
      InClosedGridRectangle
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center) point at pointInMacrocell
    simp only [InClosedGridRectangle,
      planarSATMacrocellRouteLower,
      planarSATMacrocellRouteUpper,
      planarMacroScale, Cell.add, Cell.scale] at pointInMacrocell pointInExpandedRefinement
    omega
  have baseBounds :=
    drawing_vertexPosition_in_fundamental_square graph vertexMember
  have horizontalEq :
      center.1 =
        ((drawing graph).vertexPosition graph vertex).1 +
          period * translate.1 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have verticalEq :
      center.2 =
        ((drawing graph).vertexPosition graph vertex).2 +
          period * translate.2 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  constructor
  · exact fundamental_translate_shift_is_neighbor
      periodPositive baseBounds.1 baseBounds.2.1
      centerBounds.1 centerBounds.2.1 horizontalEq
  · exact fundamental_translate_shift_is_neighbor
      periodPositive baseBounds.2.2.1 baseBounds.2.2.2
      centerBounds.2.2.1 centerBounds.2.2.2 verticalEq

/-- A segment in the refined expanded square cannot meet a segment in the
macrocell of a non-neighboring lifted vertex.  This continuous formulation
avoids choosing an integer intersection point: separated closed endpoint
boxes directly contradict `InteriorsMeet`. -/
theorem liftedDrawingVertexPosition_translate_neighbor_of_macrocellSegment_meets_expanded
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices)
    (translate : Cell)
    (expandedSegment macrocellSegment : GridSegment)
    (expandedStart :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < expandedSegment.start.1 ∧
        expandedSegment.start.1 < 2 * period ∧
        -period < expandedSegment.start.2 ∧
        expandedSegment.start.2 < 2 * period)
    (expandedFinish :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < expandedSegment.finish.1 ∧
        expandedSegment.finish.1 < 2 * period ∧
        -period < expandedSegment.finish.2 ∧
        expandedSegment.finish.2 < 2 * period)
    (macrocellStart :
      InPlanarSATMacrocell
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))
        macrocellSegment.start)
    (macrocellFinish :
      InPlanarSATMacrocell
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))
        macrocellSegment.finish)
    (meet :
      GridSegment.InteriorsMeet expandedSegment macrocellSegment) :
    IsNeighborTranslation translate := by
  let period : Int := drawingGridSize graph
  let refinedPeriod : Int := planarMacroScale * period
  let center :=
    Cell.add
      ((drawing graph).vertexPosition graph vertex)
      ((drawing graph).periodTranslation translate)
  let expandedLower : Cell :=
    (-refinedPeriod + 1, -refinedPeriod + 1)
  let expandedUpper : Cell :=
    (2 * refinedPeriod - 1, 2 * refinedPeriod - 1)
  have periodPositive : 0 < period := by
    dsimp only [period]
    exact_mod_cast drawingGridSize_pos graph
  have baseBounds :=
    drawing_vertexPosition_in_fundamental_square graph vertexMember
  change
    0 < ((drawing graph).vertexPosition graph vertex).1 ∧
      ((drawing graph).vertexPosition graph vertex).1 < period ∧
      0 < ((drawing graph).vertexPosition graph vertex).2 ∧
      ((drawing graph).vertexPosition graph vertex).2 < period at baseBounds
  have centerHorizontal :
      center.1 =
        ((drawing graph).vertexPosition graph vertex).1 +
          period * translate.1 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have centerVertical :
      center.2 =
        ((drawing graph).vertexPosition graph vertex).2 +
          period * translate.2 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  by_contra notNeighbor
  have translateOutside :
      translate.1 ≤ -2 ∨ 2 ≤ translate.1 ∨
        translate.2 ≤ -2 ∨ 2 ≤ translate.2 := by
    rcases translate with ⟨horizontal, vertical⟩
    simp only [IsNeighborTranslation] at notNeighbor
    omega
  have rectanglesSeparated :
      ClosedGridRectanglesSeparated
        expandedLower expandedUpper
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center) := by
    rcases translateOutside with
        horizontalLow | horizontalHigh | verticalLow | verticalHigh
    · have nonnegative :
          0 ≤ period * (-translate.1 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productUpper :
          period * translate.1 ≤ -2 * period := by
        nlinarith
      have centerUpper : center.1 ≤ -period - 1 := by
        rw [centerHorizontal]
        have baseUpperInt :
            ((drawing graph).vertexPosition graph vertex).1 ≤
              period - 1 := by
          omega
        omega
      apply Or.inr
      apply Or.inl
      simp only [expandedLower,
        planarSATMacrocellRouteUpper,
        refinedPeriod, planarMacroScale,
        Cell.add, Cell.scale]
      omega
    · have nonnegative :
          0 ≤ period * (translate.1 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productLower :
          2 * period ≤ period * translate.1 := by
        nlinarith
      have centerLower : 2 * period + 1 ≤ center.1 := by
        rw [centerHorizontal]
        omega
      apply Or.inl
      simp only [expandedUpper,
        planarSATMacrocellRouteLower,
        refinedPeriod, planarMacroScale,
        Cell.scale]
      omega
    · have nonnegative :
          0 ≤ period * (-translate.2 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productUpper :
          period * translate.2 ≤ -2 * period := by
        nlinarith
      have centerUpper : center.2 ≤ -period - 1 := by
        rw [centerVertical]
        have baseUpperInt :
            ((drawing graph).vertexPosition graph vertex).2 ≤
              period - 1 := by
          omega
        omega
      apply Or.inr
      apply Or.inr
      apply Or.inr
      simp only [expandedLower,
        planarSATMacrocellRouteUpper,
        refinedPeriod, planarMacroScale,
        Cell.add, Cell.scale]
      omega
    · have nonnegative :
          0 ≤ period * (translate.2 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productLower :
          2 * period ≤ period * translate.2 := by
        nlinarith
      have centerLower : 2 * period + 1 ≤ center.2 := by
        rw [centerVertical]
        omega
      apply Or.inr
      apply Or.inr
      apply Or.inl
      simp only [expandedUpper,
        planarSATMacrocellRouteLower,
        refinedPeriod, planarMacroScale,
        Cell.scale]
      omega
  have expandedStartBounded :
      InClosedGridRectangle
        expandedLower expandedUpper expandedSegment.start := by
    simp only [InClosedGridRectangle, expandedLower,
      expandedUpper, refinedPeriod, period] at expandedStart ⊢
    omega
  have expandedFinishBounded :
      InClosedGridRectangle
        expandedLower expandedUpper expandedSegment.finish := by
    simp only [InClosedGridRectangle, expandedLower,
      expandedUpper, refinedPeriod, period] at expandedFinish ⊢
    omega
  exact
    (not_interiorsMeet_of_inClosedGridRectangles_of_separated
      expandedStartBounded expandedFinishBounded
      macrocellStart macrocellFinish rectanglesSeparated)
      meet

/-- Translation by a fixed cell is injective on grid segments. -/
theorem GridSegment.translate_injective (offset : Cell) :
    Function.Injective (fun segment : GridSegment =>
      segment.translate offset) := by
  intro first second translatedEq
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [GridSegment.translate, Cell.add,
    GridSegment.mk.injEq, Prod.mk.injEq] at translatedEq ⊢
  omega

/-- The final indexed carrier segment is already the finite physical
segment with its source clause anchor removed.  This is the source
normalization whose endpoints retain the final expanded-square bound. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.indexedSegment_eq_anchorNormalizedPhysical
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    indexed.segment =
      witness.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.neg witness.sourceClauseAnchor)) := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have sourceShiftEq :
      Cell.sub witness.physicalShift shift =
        Cell.neg witness.sourceClauseAnchor := by
    rcases shift with ⟨shiftX, shiftY⟩
    simp [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      Cell.sub, Cell.neg]
  have normalizedThenShift :=
    segment_translate_placement_sub_add
      placement witness.physicalSegment witness.physicalShift shift
  rw [sourceShiftEq] at normalizedThenShift
  have normalizedEq :
      indexed.segment =
        witness.physicalSegment.translate
          (placement.translation
            (Cell.neg witness.sourceClauseAnchor)) := by
    apply GridSegment.translate_injective
      (placement.translation shift)
    change
      indexed.segment.translate (placement.translation shift) =
        (witness.physicalSegment.translate
          (placement.translation
            (Cell.neg witness.sourceClauseAnchor))).translate
              (placement.translation shift)
    rw [normalizedThenShift]
    exact witness.segmentEq
  have offsetEq :
      placement.translation
          (Cell.neg witness.sourceClauseAnchor) =
        carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.neg witness.sourceClauseAnchor) :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula (Cell.neg witness.sourceClauseAnchor)
  simpa only [offsetEq] using normalizedEq

/-- Undo the two quotient gauges in a final contact, then cancel the carrier's
common physical translate.  The result is a contact between the carrier's
original finite segment and the noncarrier segment translated by exactly the
source shift used by the halo-closure reduction below. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.alignedPhysicalSegments_interiorsMeet_of_final
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    GridSegment.InteriorsMeet
      first.physicalSegment
      (second.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub second.physicalShift first.physicalShift))) := by
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq,
    secondRepresentative.segmentEq] at meet
  change
    GridSegment.InteriorsMeet
      (first.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation first.physicalShift))
      (second.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation second.physicalShift)) at meet
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let sourceShift :=
    Cell.sub second.physicalShift first.physicalShift
  have secondAlignedEq :
      (second.physicalSegment.translate
        (placement.translation sourceShift)).translate
          (placement.translation first.physicalShift) =
        second.physicalSegment.translate
          (placement.translation second.physicalShift) := by
    exact segment_translate_placement_sub_add
      placement second.physicalSegment
      second.physicalShift first.physicalShift
  rw [← secondAlignedEq] at meet
  have aligned :
      GridSegment.InteriorsMeet
        first.physicalSegment
        (second.physicalSegment.translate
          (placement.translation sourceShift)) :=
    (GridSegment.interiorsMeet_translate_both_iff
      first.physicalSegment
      (second.physicalSegment.translate
        (placement.translation sourceShift))
      (placement.translation first.physicalShift)).mp meet
  have offsetEq :
      placement.translation sourceShift =
        carrierMacroPeriodTranslation
          formula.incidenceGraph sourceShift :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula sourceShift
  simpa only [sourceShift, offsetEq] using aligned

/-- Cancel the carrier's final lattice translate while keeping its indexed
segment anchor-normalized.  The other physical source is then shifted by its
physical shift minus the carrier's final shift. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.anchorAlignedPhysical_interiorsMeet_of_final
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    GridSegment.InteriorsMeet
      firstIndexed.segment
      (second.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub second.physicalShift firstShift))) := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let relativePhysicalShift :=
    Cell.sub second.physicalShift first.physicalShift
  let anchorShift := Cell.neg first.sourceClauseAnchor
  let targetShift := Cell.sub second.physicalShift firstShift
  have alignedPhysical :
      GridSegment.InteriorsMeet
        first.physicalSegment
        (second.physicalSegment.translate
          (placement.translation relativePhysicalShift)) := by
    have aligned :=
      first.alignedPhysicalSegments_interiorsMeet_of_final second meet
    have offsetEq :
        placement.translation relativePhysicalShift =
          carrierMacroPeriodTranslation formula.incidenceGraph
            relativePhysicalShift :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula relativePhysicalShift
    simpa only [relativePhysicalShift, offsetEq] using aligned
  have shiftedMeet :
      GridSegment.InteriorsMeet
        (first.physicalSegment.translate
          (placement.translation anchorShift))
        ((second.physicalSegment.translate
          (placement.translation relativePhysicalShift)).translate
            (placement.translation anchorShift)) :=
    (GridSegment.interiorsMeet_translate_both_iff
      first.physicalSegment
      (second.physicalSegment.translate
        (placement.translation relativePhysicalShift))
      (placement.translation anchorShift)).mpr alignedPhysical
  have relativeShiftEq :
      Cell.sub targetShift anchorShift = relativePhysicalShift := by
    rcases firstShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    rcases first.sourceClauseAnchor with ⟨anchorX, anchorY⟩
    simp only [targetShift, anchorShift, relativePhysicalShift,
      FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      Cell.sub, Cell.neg, Prod.mk.injEq]
    constructor <;> ring
  have secondShiftedEq :
      (second.physicalSegment.translate
        (placement.translation relativePhysicalShift)).translate
          (placement.translation anchorShift) =
        second.physicalSegment.translate
          (placement.translation targetShift) := by
    have translated :=
      segment_translate_placement_sub_add
        placement second.physicalSegment targetShift anchorShift
    rwa [relativeShiftEq] at translated
  have firstEq :
      first.physicalSegment.translate
          (placement.translation anchorShift) =
        firstIndexed.segment := by
    rw [first.indexedSegment_eq_anchorNormalizedPhysical]
    have offsetEq :
        placement.translation anchorShift =
          carrierMacroPeriodTranslation formula.incidenceGraph
            anchorShift :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula anchorShift
    simp only [anchorShift, offsetEq]
  have targetOffsetEq :
      placement.translation targetShift =
        carrierMacroPeriodTranslation formula.incidenceGraph
          targetShift :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula targetShift
  simpa only [firstEq, secondShiftedEq, targetShift,
    targetOffsetEq] using shiftedMeet

/-- Translating a noncarrier witness's physical segment translates both
endpoint macrocell certificates by the same drawing-period shift. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.translatedPhysicalSegment_endpoints_in_macrocell
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (notCarrier :
      ¬∃ link,
        witness.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link)
    (center : Cell)
    (centerEq :
      witness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some center)
    (sourceShift : Cell) :
    let translatedSegment :=
      witness.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph sourceShift)
    InPlanarSATMacrocell
        (Cell.add center
          ((drawing formula.incidenceGraph).periodTranslation sourceShift))
        translatedSegment.start ∧
      InPlanarSATMacrocell
        (Cell.add center
          ((drawing formula.incidenceGraph).periodTranslation sourceShift))
        translatedSegment.finish := by
  have valid :=
    witness.routeWitness.metadata
      |>.valid_of_retainedValid_of_not_carrier
        witness.metadata_retainedValid notCarrier
  have endpointMembers :=
    gridPolylineSegments_endpoints_mem
      (List.fst_mem_of_mem_zipIdx
        witness.physicalSegment_mem_sourceRoute)
  have startBounded :=
    witness.routeWitness.metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal valid center centerEq
      witness.routeWitness.literalMember endpointMembers.1
  have finishBounded :=
    witness.routeWitness.metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal valid center centerEq
      witness.routeWitness.literalMember endpointMembers.2
  have translatedStart :=
    inPlanarSATMacrocell_translate
      (shift := sourceShift)
      (drawingGridSize formula.incidenceGraph) startBounded
  have translatedFinish :=
    inPlanarSATMacrocell_translate
      (shift := sourceShift)
      (drawingGridSize formula.incidenceGraph) finishBounded
  constructor
  · simpa [GridSegment.translate,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale, planarMacroScale,
      add_comm, mul_assoc, mul_comm, mul_left_comm] using translatedStart
  · simpa [GridSegment.translate,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale, planarMacroScale,
      add_comm, mul_assoc, mul_comm, mul_left_comm] using translatedFinish

/-- The final gauged drawing has exactly the refined planar-SAT period used
by the macrocell contact bounds. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_gridSize_int
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).gridSize : Int) =
      planarMacroScale * drawingGridSize formula.incidenceGraph := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have periodPositive : 0 < placement.period := by
    simpa [placement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have gridSizeEq :
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).gridSize =
        placement.period := by
    simpa [
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
      using
        PositionedPeriodicCNF.incidenceDrawing_gridSize
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          placement
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          periodPositive
  rw [gridSizeEq]
  simp [placement,
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
    wrappedDrawingPeriodicPlanarSATPlacement,
    drawingPeriodicPlanarSATPlacement,
    planarMacroScale]

/-- For any retained noncarrier clause, the source-clause anchor is the
coordinatewise drawing-period quotient of its component's macrocell center.
Thus the gauging translation normalizes the entire component occurrence, not
just the chosen clause position. -/
theorem
    DrawingPlanarSATClauseMetadata.sourceClauseAnchor_eq_macrocellCenter_ediv
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (nonempty : metadata.clause.literals ≠ []) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      (center.1 / drawingGridSize formula.incidenceGraph,
        center.2 / drawingGridSize formula.incidenceGraph) := by
  have clauseBounded :=
    metadata.retainedClausePosition_in_macrocell
      wellFormed degree isLocal valid center centerEq nonempty
  have centerBounded :
      InPlanarSATMacrocell center
        (Cell.scale planarMacroScale center) := by
    rcases center with ⟨centerX, centerY⟩
    norm_num [InPlanarSATMacrocell,
      planarSATMacrocellRouteLower,
      planarSATMacrocellRouteUpper,
      InClosedGridRectangle, Cell.add, Cell.scale,
      planarMacroScale]
  have quotientEq :=
    macrocellQuotient_eq
      (periodFactor := drawingGridSize formula.incidenceGraph)
      clauseBounded centerBounded
  rw [metadata.sourceClauseAnchor_eq_position_ediv
    wellFormed degree isLocal valid nonempty]
  simpa [drawingPeriodicPlanarSATPlacement,
    planarMacroScale, Cell.scale] using quotientEq

/-- Dividing a translated half-open representative by the drawing period
recovers its lattice translation coordinatewise. -/
theorem PeriodicGridDrawing.translatedHalfOpenPosition_ediv
    (drawing : PeriodicGridDrawing)
    {base shift : Cell}
    (baseBounds :
      0 ≤ base.1 ∧ base.1 < drawing.gridSize ∧
        0 ≤ base.2 ∧ base.2 < drawing.gridSize) :
    ((Cell.add base (drawing.periodTranslation shift)).1 /
        drawing.gridSize,
      (Cell.add base (drawing.periodTranslation shift)).2 /
        drawing.gridSize) =
      shift := by
  have periodNe : (drawing.gridSize : Int) ≠ 0 := by
    have periodPositive : 0 < drawing.gridSize :=
      Nat.zero_lt_succ drawing.gridSizePred
    exact_mod_cast periodPositive.ne'
  have horizontalBaseQuotient :
      base.1 / (drawing.gridSize : Int) = 0 :=
    Int.ediv_eq_zero_of_lt baseBounds.1 baseBounds.2.1
  have verticalBaseQuotient :
      base.2 / (drawing.gridSize : Int) = 0 :=
    Int.ediv_eq_zero_of_lt baseBounds.2.2.1 baseBounds.2.2.2
  apply Prod.ext
  · simp only [Cell.add,
      PeriodicGridDrawing.periodTranslation, Cell.scale]
    rw [mul_comm, Int.add_mul_ediv_right _ _ periodNe,
      horizontalBaseQuotient]
    simp
  · simp only [Cell.add,
      PeriodicGridDrawing.periodTranslation, Cell.scale]
    rw [mul_comm, Int.add_mul_ediv_right _ _ periodNe,
      verticalBaseQuotient]
    simp

/-- The coordinatewise period quotient of a lifted incidence-graph vertex
is exactly its occurrence translation. -/
theorem liftedIncidenceVertexPosition_ediv
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {vertex : CNFVertex Variable}
    (vertexMember : vertex ∈ formula.incidenceGraph.vertices)
    (translate : Cell) :
    ((liftedIncidenceVertexPosition formula vertex translate).1 /
        drawingGridSize formula.incidenceGraph,
      (liftedIncidenceVertexPosition formula vertex translate).2 /
        drawingGridSize formula.incidenceGraph) =
      translate := by
  have vertexBounds :=
    drawing_vertexPosition_in_fundamental_square
      formula.incidenceGraph vertexMember
  have halfOpenBounds :
      0 ≤ ((drawing formula.incidenceGraph).vertexPosition
          formula.incidenceGraph vertex).1 ∧
        ((drawing formula.incidenceGraph).vertexPosition
            formula.incidenceGraph vertex).1 <
          (drawing formula.incidenceGraph).gridSize ∧
        0 ≤ ((drawing formula.incidenceGraph).vertexPosition
          formula.incidenceGraph vertex).2 ∧
        ((drawing formula.incidenceGraph).vertexPosition
            formula.incidenceGraph vertex).2 <
          (drawing formula.incidenceGraph).gridSize := by
    simpa [drawing_gridSize] using
      ⟨le_of_lt vertexBounds.1, vertexBounds.2.1,
        le_of_lt vertexBounds.2.2.1, vertexBounds.2.2.2⟩
  simpa [liftedIncidenceVertexPosition, drawing_gridSize] using
    (PeriodicGridDrawing.translatedHalfOpenPosition_ediv
      (drawing formula.incidenceGraph) halfOpenBounds)

/-- If a noncarrier component is centered at a lifted incidence-graph
vertex, its clause anchor is the occurrence translation of that vertex. -/
theorem
    DrawingPlanarSATClauseMetadata.sourceClauseAnchor_eq_liftedVertexTranslate
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (vertex : CNFVertex Variable)
    (vertexMember : vertex ∈ formula.incidenceGraph.vertices)
    (translate : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula =
        some
          (liftedIncidenceVertexPosition formula vertex translate)) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      translate := by
  rw [metadata.sourceClauseAnchor_eq_macrocellCenter_ediv
    wellFormed degree isLocal valid
    (liftedIncidenceVertexPosition formula vertex translate)
    centerEq nonempty]
  exact liftedIncidenceVertexPosition_ediv
    formula vertexMember translate

/-- A local protoedge offset is one of the nine neighboring translations. -/
theorem PeriodicEdge.offset_neighbor_of_local
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex)
    (edgeLocal : edge.span ≤ 1) :
    IsNeighborTranslation edge.offset := by
  rcases offset_eq_of_span_le_one edge edgeLocal with
    offset | offset | offset | offset | offset <;>
    simp [offset, IsNeighborTranslation]

/-- Every semantic bend-center placement of a local protoedge crosses at
most one period boundary. -/
theorem routeBendCenterPlacement_offset_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMember : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {placement : RouteBendCenterPlacement Vertex}
    (placementMember :
      placement ∈ routeBendCenterPlacements graph edge edgeIndex) :
    IsNeighborTranslation placement.offset := by
  have edgeLocal : edge.span ≤ 1 :=
    isLocal edge (List.fst_mem_of_mem_zipIdx edgeMember)
  rcases offset_eq_of_span_le_one edge edgeLocal with
    offset | offset | offset | offset | offset
  all_goals
    simp [routeBendCenterPlacements, offset] at placementMember
  all_goals
    aesop (config := { warnOnNonterminal := false }) <;>
      simp [IsNeighborTranslation]

/-- Gauging a retained bend clause by its source-clause anchor leaves the
route occurrence at the inverse of its semantic boundary offset, hence in
the neighboring route halo. -/
theorem DrawingPlanarSATClauseMetadata.bend_anchorNormalize_translate_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .bend routeBend localClauseIndex) :
    IsNeighborTranslation
      (Cell.add routeBend.translate
        (Cell.neg
          (PeriodicCNF.clauseAnchor
            (metadataGaugedPositionedClause formula metadata).literals))) := by
  let graph := formula.incidenceGraph
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have routeBendMember :
      routeBend ∈ drawingRouteBends graph :=
    List.mem_dedup.mp valid'.1
  rcases drawingRouteBend_centerPlacement
      graph isLocal routeBendMember with
    ⟨edge, edgeIndex, placement, placementIndex,
      edgeMember, placementMember, _routeIndexEq,
      _placementIndexEq, pointEq⟩
  have placementListMember :
      placement ∈ routeBendCenterPlacements graph edge edgeIndex :=
    List.fst_mem_of_mem_zipIdx placementMember
  have placementValid :
      placement.kind.Valid graph :=
    routeBendCenterPlacements_kind_valid
      edgeMember placementListMember
  have placementBounds :=
    RouteBendCenterKind.position_in_fundamental
      wellFormed degree placementValid
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some (routeBend.drawingPoint graph) := by
    rw [sourceEq]
    rfl
  have anchorEq :=
    metadata.sourceClauseAnchor_eq_macrocellCenter_ediv
      wellFormed degree isLocal valid
      (routeBend.drawingPoint graph) centerEq nonempty
  have pointQuotient :
      ((routeBend.drawingPoint graph).1 / drawingGridSize graph,
        (routeBend.drawingPoint graph).2 / drawingGridSize graph) =
        Cell.add routeBend.translate placement.offset := by
    rw [pointEq]
    simpa [drawing_gridSize] using
      (PeriodicGridDrawing.translatedHalfOpenPosition_ediv
        (drawing graph) placementBounds)
  have normalizedTranslateEq :
      Cell.add routeBend.translate
          (Cell.neg
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause formula metadata).literals)) =
        Cell.neg placement.offset := by
    rw [anchorEq, pointQuotient]
    rcases routeBend.translate with ⟨routeX, routeY⟩
    rcases placement.offset with ⟨offsetX, offsetY⟩
    simp [Cell.add, Cell.neg, Cell.sub]
  rw [normalizedTranslateEq]
  exact
    (routeBendCenterPlacement_offset_neighbor
      isLocal edgeMember placementListMember).neg

/-- The anchor-normalized representative of every retained bend source is
itself retained in the finite neighboring bend family. -/
theorem DrawingPlanarSATClauseMetadata.bend_anchorNormalize_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .bend routeBend localClauseIndex) :
    (metadata.source.periodTranslate formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
        |>.RetainedComponentMember formula) := by
  have sourceMember :
      (DrawingPlanarSATClauseSource.bend
        routeBend localClauseIndex).RetainedComponentMember formula := by
    have valid' := valid
    unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
    rw [sourceEq] at valid'
    exact valid'.1
  rw [sourceEq]
  exact
    bendSource_periodTranslate_retainedComponentMember_of_neighbor
      formula routeBend localClauseIndex sourceMember
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
      (metadata.bend_anchorNormalize_translate_neighbor
        wellFormed degree isLocal valid nonempty
        routeBend localClauseIndex sourceEq)

/-- A retained crossover clause uses its crossing point as macrocell center,
so its source-clause anchor is exactly the crossing's extracted period
shift. -/
theorem DrawingPlanarSATClauseMetadata.crossover_sourceClauseAnchor_eq_periodShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .crossover crossing localClauseIndex) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      crossingPeriodShift formula.incidenceGraph crossing := by
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some crossing.point := by
    rw [sourceEq]
    rfl
  simpa [crossingPeriodShift] using
    (metadata.sourceClauseAnchor_eq_macrocellCenter_ediv
      wellFormed degree isLocal valid crossing.point centerEq nonempty)

/-- Anchor-normalizing a retained crossover source is exactly periodic
normalization of its crossing record, which is a canonical oriented
crossing and hence remains in the retained crossing halo. -/
theorem
    DrawingPlanarSATClauseMetadata.crossover_anchorNormalize_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .crossover crossing localClauseIndex) :
    (metadata.source.periodTranslate formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
        |>.RetainedComponentMember formula) := by
  let graph := formula.incidenceGraph
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have normalizedMember :
      crossing.periodNormalize graph ∈ orientedCrossingHalo graph :=
    orientedCrossings_subset_orientedCrossingHalo graph
      (periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal valid'.1)
  rw [sourceEq,
    metadata.crossover_sourceClauseAnchor_eq_periodShift
      wellFormed degree isLocal valid nonempty
      crossing localClauseIndex sourceEq]
  apply crossoverSource_periodTranslate_retainedComponentMember
  rw [CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize]
  exact normalizedMember

/-- A retained routed-clause source is centered at its lifted clause site,
so anchor normalization moves that site to the zero occurrence and keeps it
in the retained neighboring site family. -/
theorem
    DrawingPlanarSATClauseMetadata.routedClause_anchorNormalize_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (site : ClauseRouteSite)
    (sourceEq : metadata.source = .routedClause site) :
    (metadata.source.periodTranslate formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
        |>.RetainedComponentMember formula) := by
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2) := by
    rw [sourceEq]
    rfl
  have anchorEq :=
    metadata.sourceClauseAnchor_eq_liftedVertexTranslate
      wellFormed degree isLocal valid nonempty
      (.clause site.1)
      (drawingClauseRouteSite_vertex_mem formula valid'.1)
      site.2 centerEq
  rw [sourceEq, anchorEq]
  apply
    routedClauseSource_periodTranslate_retainedComponentMember_of_neighbor
      formula site valid'.1 (Cell.neg site.2)
  rcases site.2 with ⟨siteX, siteY⟩
  simp [Cell.add, Cell.neg, Cell.sub, IsNeighborTranslation]

/-- Anchor normalization of a retained routed-variable arm leaves its
witnessing route occurrence at the inverse local protoedge offset.  This is
the neighboring orbit condition needed to reindex the arm, even when the
sorted arm index itself changes. -/
theorem
    DrawingPlanarSATClauseMetadata.routedVariable_anchorNormalize_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source =
        .routedVariable site armIndex arm link localClauseIndex) :
    metadata.source.RetainedOrbitCondition formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals)) := by
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  rcases
      exists_routeOccurrence_of_routedVariableLinkMember
        formula site valid'.2.1 with
    ⟨occurrence, occurrenceMember, linkFirstEq⟩
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2) := by
    rw [sourceEq]
    rfl
  have anchorEq :=
    metadata.sourceClauseAnchor_eq_liftedVertexTranslate
      wellFormed degree isLocal valid nonempty
      (.variable site.1)
      (drawingVariableRouteSite_vertex_mem formula valid'.1)
      site.2 centerEq
  rw [sourceEq, anchorEq]
  refine ⟨occurrence, occurrenceMember, linkFirstEq, ?_⟩
  have siteTranslateEq :
      Cell.add occurrence.translate occurrence.edge.offset = site.2 :=
    congrArg Prod.snd occurrenceData.2
  have edgeMember :=
    occurrence.taggedEdge_mem formula occurrenceData.1
  have edgeLocal : occurrence.edge.span ≤ 1 :=
    isLocal occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have offsetNeighbor :
      IsNeighborTranslation occurrence.edge.offset :=
    PeriodicEdge.offset_neighbor_of_local
      occurrence.edge edgeLocal
  have normalizedTranslateEq :
      Cell.add occurrence.translate (Cell.neg site.2) =
        Cell.neg occurrence.edge.offset := by
    rw [← siteTranslateEq]
    rcases occurrence.translate with ⟨translateX, translateY⟩
    rcases occurrence.edge.offset with ⟨offsetX, offsetY⟩
    simp [Cell.add, Cell.neg, Cell.sub]
  rw [normalizedTranslateEq]
  exact offsetNeighbor.neg

/-- Every retained noncarrier source satisfies its family-specific orbit
condition after subtracting its source-clause anchor.  Exact translated
membership handles crossovers, bends, and routed clauses; routed-variable
arms use the occurrence witness above because their sorted arm index may
change. -/
theorem
    DrawingPlanarSATClauseMetadata.noncarrier_anchorNormalize_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (notCarrier :
      ¬∃ link,
        metadata.source.component =
          DrawingPlanarSATComponent.carrier link) :
    metadata.source.RetainedOrbitCondition formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals)) := by
  let anchorShift :=
    Cell.neg
      (PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals)
  have sourceMember :
      metadata.source.RetainedComponentMember formula :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid |>.1
  cases sourceEq : metadata.source with
  | crossover crossing localClauseIndex =>
      rw [← sourceEq]
      change metadata.source.RetainedOrbitCondition formula anchorShift
      apply
        metadata.source.retainedOrbitCondition_of_periodTranslate_mem
          formula sourceMember anchorShift
      simpa only [anchorShift] using
        (metadata.crossover_anchorNormalize_retainedComponentMember
          wellFormed degree isLocal valid nonempty
          crossing localClauseIndex sourceEq)
  | carrier link localClauseIndex =>
      exfalso
      apply notCarrier
      refine ⟨link, ?_⟩
      rw [sourceEq]
      rfl
  | bend routeBend localClauseIndex =>
      rw [← sourceEq]
      change metadata.source.RetainedOrbitCondition formula anchorShift
      apply
        metadata.source.retainedOrbitCondition_of_periodTranslate_mem
          formula sourceMember anchorShift
      simpa only [anchorShift] using
        (metadata.bend_anchorNormalize_retainedComponentMember
          wellFormed degree isLocal valid nonempty
          routeBend localClauseIndex sourceEq)
  | routedClause site =>
      rw [← sourceEq]
      change metadata.source.RetainedOrbitCondition formula anchorShift
      apply
        metadata.source.retainedOrbitCondition_of_periodTranslate_mem
          formula sourceMember anchorShift
      simpa only [anchorShift] using
        (metadata.routedClause_anchorNormalize_retainedComponentMember
          wellFormed degree isLocal valid nonempty site sourceEq)
  | routedVariable site armIndex arm link localClauseIndex =>
      rw [← sourceEq]
      simpa only [anchorShift] using
        (metadata.routedVariable_anchorNormalize_retainedOrbitCondition
          wellFormed degree isLocal valid nonempty
          site armIndex arm link localClauseIndex sourceEq)

/-- A contact with an anchor-normalized final carrier segment forces a
translated routed-clause source to remain in the neighboring retained
site family. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.translated_routedClause_retained_of_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (site : ClauseRouteSite)
    (secondSourceEq :
      second.routeWitness.metadata.source = .routedClause site)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    (second.routeWitness.metadata.source.periodTranslate formula
      (Cell.sub second.physicalShift firstShift)
        |>.RetainedComponentMember formula) := by
  let graph := formula.incidenceGraph
  let sourceShift := Cell.sub second.physicalShift firstShift
  have secondNotCarrier :
      ¬∃ link,
        second.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link := by
    rintro ⟨link, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have siteMember :
      site ∈ drawingClauseRouteSites formula := by
    have sourceMember := second.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2) := by
    rw [secondSourceEq]
    rfl
  have translatedEndpoints :=
    second.translatedPhysicalSegment_endpoints_in_macrocell
      wellFormed degree isLocal secondNotCarrier
      (liftedIncidenceVertexPosition
        formula (.clause site.1) site.2)
      centerEq sourceShift
  rw [liftedIncidenceVertexPosition_add_periodTranslation
    formula (.clause site.1) site.2 sourceShift] at translatedEndpoints
  have finalEndpointBounds :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsInExpandedSquare
      formula wellFormed degree isLocal clausesNonempty
      firstIndexed firstMember
  have expandedStart :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < firstIndexed.segment.start.1 ∧
        firstIndexed.segment.start.1 < 2 * period ∧
        -period < firstIndexed.segment.start.2 ∧
        firstIndexed.segment.start.2 < 2 * period := by
    simpa only [PeriodicGridDrawing.PositionInExpandedSquare,
      graph,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_gridSize_int]
      using finalEndpointBounds.1
  have expandedFinish :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < firstIndexed.segment.finish.1 ∧
        firstIndexed.segment.finish.1 < 2 * period ∧
        -period < firstIndexed.segment.finish.2 ∧
        firstIndexed.segment.finish.2 < 2 * period := by
    simpa only [PeriodicGridDrawing.PositionInExpandedSquare,
      graph,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_gridSize_int]
      using finalEndpointBounds.2
  have aligned :=
    first.anchorAlignedPhysical_interiorsMeet_of_final second meet
  have translatedNeighbor :
      IsNeighborTranslation (Cell.add site.2 sourceShift) := by
    exact
      liftedDrawingVertexPosition_translate_neighbor_of_macrocellSegment_meets_expanded
        graph
        (drawingClauseRouteSite_vertex_mem formula siteMember)
        (Cell.add site.2 sourceShift)
        firstIndexed.segment
        (second.physicalSegment.translate
          (carrierMacroPeriodTranslation graph sourceShift))
        expandedStart expandedFinish
        translatedEndpoints.1 translatedEndpoints.2 aligned
  rw [secondSourceEq]
  exact
    routedClauseSource_periodTranslate_retainedComponentMember_of_neighbor
      formula site siteMember sourceShift translatedNeighbor

/-- A retained carrier metadata source supplies the raw-link membership and
neighboring first occurrence required by the finite carrier separation API. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.carrier_source_raw_and_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.routeWitness.metadata.source.component = .carrier link) :
    link ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph ∧
      IsNeighborTranslation link.first.translate := by
  rcases
      witness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have sourceMember :=
    witness.source_retainedComponentMember
  rw [sourceEq] at sourceMember
  have selectedMember :
      link ∈
        retainedDrawingCompleteCarrierLinks formula.incidenceGraph := by
    simpa only [
      DrawingPlanarSATClauseSource.RetainedComponentMember] using
      sourceMember
  exact
    ⟨((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph link).mp selectedMember).1,
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        formula.incidenceGraph selectedMember⟩

/-- Anchor-normalizing the carrier source and translating the noncarrier
source by its physical shift minus the carrier's final shift leaves the same
external translate on both finite routes.  Retention of that translated
noncarrier therefore contradicts raw-carrier planarity. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_anchor_carrier_noncarrier_of_contact_retained
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (contactRetained :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        (second.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub second.physicalShift firstShift)
            |>.RetainedComponentMember formula)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  let carrierShift := Cell.neg first.sourceClauseAnchor
  let secondSourceShift := Cell.sub second.physicalShift firstShift
  have translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link carrierShift ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
    exact
      first.routeWitness.metadata.carrier_anchorNormalize_mem_raw
        wellFormed degree isLocal first.metadata_retainedValid
        firstNonempty link localClauseIndex firstSourceEq
  have translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link carrierShift).first.translate) := by
    exact
      first.routeWitness.metadata.carrier_first_anchorNormalize_translate_neighbor
        wellFormed degree isLocal first.metadata_retainedValid
        firstNonempty link localClauseIndex firstSourceEq
  have commonShiftEq :
      Cell.sub first.physicalShift carrierShift =
        Cell.sub second.physicalShift secondSourceShift := by
    have firstCommon :
        Cell.sub first.physicalShift carrierShift = firstShift := by
      rcases firstShift with ⟨firstX, firstY⟩
      simp [carrierShift,
        FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
        Cell.sub, Cell.neg]
    have secondCommon :
        Cell.sub second.physicalShift secondSourceShift =
          firstShift := by
      have cellSubSelf (cell base : Cell) :
          Cell.sub cell (Cell.sub cell base) = base := by
        rcases cell with ⟨cellX, cellY⟩
        rcases base with ⟨baseX, baseY⟩
        simp [Cell.sub]
      exact cellSubSelf second.physicalShift firstShift
    rw [firstCommon, secondCommon]
  intro meet
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw
      formula wellFormed degree isLocal first second
      carrierShift secondSourceShift commonShiftEq
      link firstComponentEq secondNotCarrier
      translatedLinkMember translatedFirstNeighbor
      (contactRetained meet))
      meet

/-- Final carrier segments have disjoint interiors from every routed-clause
segment occurrence, at arbitrary quotient translates. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (site : ClauseRouteSite)
    (secondSourceEq :
      second.routeWitness.metadata.source = .routedClause site) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_anchor_carrier_noncarrier_of_contact_retained
      formula wellFormed degree isLocal first second
      link firstComponentEq secondNotCarrier
  intro meet
  exact
    FinalGaugedSegmentOccurrenceWitness.translated_routedClause_retained_of_contact
      formula wellFormed degree isLocal clausesNonempty
      firstMember first second site secondSourceEq meet

/-- If a hypothetical final carrier--noncarrier contact keeps the physically
aligned noncarrier source in the retained halo, finite raw-carrier planarity
already gives a contradiction. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_contact_retained
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (contactRetained :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        (second.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub second.physicalShift first.physicalShift)
            |>.RetainedComponentMember formula)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  intro meet
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have commonShiftEq :
      Cell.sub first.physicalShift (0, 0) =
        Cell.sub second.physicalShift
          (Cell.sub second.physicalShift first.physicalShift) := by
    rcases first.physicalShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    simp only [Cell.sub, Prod.mk.injEq]
    constructor <;> ring
  have translatedLinkEq :
      carrierLinkPeriodTranslate formula.incidenceGraph link (0, 0) =
        link := by
    rcases link with ⟨firstNode, secondNode, positions⟩
    rcases firstNode with firstBoundary | firstTerminal <;>
      rcases secondNode with secondBoundary | secondTerminal <;>
      simp [carrierLinkPeriodTranslate,
        CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        CrossingBoundary.periodTranslate,
        CrossingRecord.periodTranslate,
        EqualityPositions.periodTranslate,
        carrierMacroPeriodTranslation,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale]
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw
      formula wellFormed degree isLocal first second
      (0, 0) (Cell.sub second.physicalShift first.physicalShift)
      commonShiftEq link firstComponentEq secondNotCarrier
      (by simpa only [translatedLinkEq] using carrierData.1)
      (by simpa using carrierData.2)
      (contactRetained meet))
      meet

/-- Equivalently, any hypothetical contact would force the physically aligned
noncarrier source outside the retained halo.  Later family-specific geometry
will contradict this escape conclusion. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_translated_noncarrier_not_retained_of_carrier_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    ¬((second.routeWitness.metadata.source.periodTranslate formula
        (Cell.sub second.physicalShift first.physicalShift))
          |>.RetainedComponentMember formula) := by
  intro translatedMember
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_contact_retained
      formula wellFormed degree isLocal first second link
      firstComponentEq secondNotCarrier
      (fun _ => translatedMember))
      meet

end PeriodicOrthocrossing
end LeanTrominoes

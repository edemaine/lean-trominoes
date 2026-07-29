import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierPeriodicSeparation

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

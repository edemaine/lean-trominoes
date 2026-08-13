/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalDegree
import LeanTrominoes.PeriodicGridDrawingRibbonSeparation
import LeanTrominoes.PlanarThreeSATEqualityLinkLens

/-!
# Equality-lens geometry on complete carriers

Complete carrier links are sorted along one translated drawing segment.
This file proves that their physical endpoints have enough forward clearance
for the equality-lens template, and then instantiates the generic positioned
link certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The indexed drawing segment supporting either kind of carrier node. -/
def CarrierNode.indexed : CarrierNode → IndexedGridSegment
  | CarrierNode.boundary item => item.indexed
  | CarrierNode.terminal item => item.indexed

/-- The periodic occurrence translate supporting either kind of carrier
node. -/
def CarrierNode.translate : CarrierNode → Cell
  | CarrierNode.boundary item => item.translate
  | CarrierNode.terminal item => item.translate

/-- Both carrier-node constructors encode their occurrence key by the same
indexed-segment/translate pair. -/
@[simp]
theorem CarrierNode.carrierKey_eq_indexed_translate
    (node : CarrierNode) :
    node.carrierKey =
      PeriodicGridDrawing.SegmentOccurrenceKey
        node.indexed node.translate := by
  cases node with
  | boundary boundary =>
      exact CrossingBoundary.carrierKey_eq_indexed_translate boundary
  | terminal terminal =>
      rfl

/-- Every listed carrier node is supported by a listed indexed segment. -/
theorem carrierNode_indexed_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph) :
    node.indexed ∈ (drawing graph).indexedSegments := by
  cases node with
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at nodeMem
        simpa using nodeMem
      exact
        (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
          graph boundaryMem).1
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold drawingCarrierNodes at nodeMem
        simpa using nodeMem
      exact (drawingSegmentTerminal_indexed_mem graph terminalMem).1

/-- Equal carrier keys recover the complete supporting occurrence data. -/
theorem carrierNode_indexed_translate_eq_of_carrierKey_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CarrierNode}
    (firstMem : first ∈ drawingCarrierNodes graph)
    (secondMem : second ∈ drawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey) :
    first.indexed = second.indexed ∧
      first.translate = second.translate := by
  rw [CarrierNode.carrierKey_eq_indexed_translate,
    CarrierNode.carrierKey_eq_indexed_translate] at keyEqual
  have routeEqual :
      first.indexed.routeIndex = second.indexed.routeIndex :=
    congrArg Prod.fst keyEqual
  have segmentEqual :
      first.indexed.segmentIndex = second.indexed.segmentIndex :=
    congrArg (fun key => key.2.1) keyEqual
  have indexedEqual :=
    indexedSegment_eq_of_indices_eq (drawing graph)
      (carrierNode_indexed_mem graph firstMem)
      (carrierNode_indexed_mem graph secondMem)
      routeEqual segmentEqual
  refine ⟨indexedEqual, ?_⟩
  exact congrArg (fun key => key.2.2) keyEqual

/-- Drawing-grid point whose macrocell contains a carrier node. -/
def CarrierNode.drawingPoint
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : CarrierNode → Cell
  | CarrierNode.boundary item => item.crossing.point
  | CarrierNode.terminal item => item.drawingPoint graph

/-- Port coordinate inside a carrier node's `20 × 20` macrocell. -/
def CarrierNode.localPosition : CarrierNode → Cell
  | CarrierNode.boundary item => item.side.localPosition
  | CarrierNode.terminal item =>
      segmentTerminalLocalPosition
        item.indexed.segment item.endpoint

/-- Carrier positions uniformly consist of a scaled drawing point and a
local port. -/
theorem CarrierNode.position_eq_scale_add_local
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (node : CarrierNode) :
    node.position graph =
      Cell.add
        (Cell.scale planarMacroScale (node.drawingPoint graph))
        node.localPosition := by
  cases node with
  | boundary boundary =>
      simp [CarrierNode.position, CarrierNode.drawingPoint,
        CarrierNode.localPosition, CrossingBoundary.position,
        crossingMacroOrigin]
  | terminal terminal =>
      rfl

/-- A listed carrier node's drawing point lies on its translated supporting
segment, allowing terminals at the closed endpoints. -/
theorem carrierNode_drawingPoint_contains
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    (node.indexed.segment.translate
        ((drawing graph).periodTranslation node.translate)).Contains
      (node.drawingPoint graph) := by
  cases node with
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at nodeMem
        simpa using nodeMem
      simpa [CarrierNode.indexed, CarrierNode.translate,
        CarrierNode.drawingPoint] using
        GridSegment.contains_of_interiorContains
          (drawingCrossingBoundary_point_data graph boundaryMem).2
  | terminal terminal =>
      simp only [CarrierNode.indexed] at axisAligned
      have translatedAligned :
          (terminal.indexed.segment.translate
            ((drawing graph).periodTranslation
              terminal.translate)).IsAxisAligned :=
        (GridSegment.isAxisAligned_translate _ _).mpr axisAligned
      generalize endpointEqual : terminal.endpoint = endpoint
      cases endpoint with
      | start =>
          simpa [CarrierNode.indexed, CarrierNode.translate,
            CarrierNode.drawingPoint,
            SegmentTerminal.drawingPoint, endpointEqual] using
            GridSegment.contains_start_of_axisAligned translatedAligned
      | finish =>
          simpa [CarrierNode.indexed, CarrierNode.translate,
            CarrierNode.drawingPoint,
            SegmentTerminal.drawingPoint, endpointEqual] using
            GridSegment.contains_finish_of_axisAligned translatedAligned

/-- On a genuine listed carrier, the node's Boolean axis tag agrees with its
supporting indexed segment. -/
theorem carrierNode_isHorizontal_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    node.isHorizontal = true ↔
      node.indexed.segment.IsHorizontal := by
  cases node with
  | terminal terminal =>
      simp [CarrierNode.isHorizontal, CarrierNode.indexed]
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at nodeMem
        simpa using nodeMem
      have crossingMem :=
        drawingCrossingBoundary_crossing_mem graph boundaryMem
      have sound := orientedCrossingHalo_sound graph crossingMem
      cases boundary with
      | mk crossing side =>
          cases side
          · have horizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                sound.2.2.2.2.2.1
            constructor
            · intro
              simpa [CarrierNode.indexed,
                CrossingBoundary.indexed] using horizontal
            · intro
              rfl
          · have horizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                sound.2.2.2.2.2.1
            constructor
            · intro
              simpa [CarrierNode.indexed,
                CrossingBoundary.indexed] using horizontal
            · intro
              rfl
          · simp only [CarrierNode.isHorizontal, CarrierNode.indexed,
              CrossingBoundary.indexed, Bool.false_eq_true,
              false_iff]
            have vertical :=
              (GridSegment.isVertical_translate _ _).mp
                sound.2.2.2.2.2.2.1
            exact fun horizontal => vertical.2 horizontal.1
          · simp only [CarrierNode.isHorizontal, CarrierNode.indexed,
              CrossingBoundary.indexed, Bool.false_eq_true,
              false_iff]
            have vertical :=
              (GridSegment.isVertical_translate _ _).mp
                sound.2.2.2.2.2.2.1
            exact fun horizontal => vertical.2 horizontal.1

/-- Every carrier port has perpendicular coordinate six and axial coordinate
congruent to one modulo ten. -/
theorem carrierNode_localPosition_axis_data
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {node : CarrierNode}
    (nodeMem : node ∈ drawingCarrierNodes graph)
    (axisAligned : node.indexed.segment.IsAxisAligned) :
    if node.isHorizontal then
      node.localPosition.2 = 6 ∧ node.localPosition.1 % 10 = 1
    else
      node.localPosition.1 = 6 ∧ node.localPosition.2 % 10 = 1 := by
  cases node with
  | boundary boundary =>
      cases boundary with
      | mk crossing side =>
          cases side <;>
            norm_num [CarrierNode.isHorizontal,
              CarrierNode.localPosition, CrossingSide.localPosition,
              CrossoverVariable.position]
  | terminal terminal =>
      simp only [CarrierNode.indexed] at axisAligned
      rcases axisAligned with horizontal | vertical
      · rcases horizontal with ⟨sameY, differentX⟩
        have horizontal' :
            terminal.indexed.segment.IsHorizontal :=
          ⟨sameY, differentX⟩
        rcases lt_or_gt_of_ne differentX with forward | backward
        · simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, horizontal', forward]
          cases terminal.endpoint <;> norm_num
        · have notForward :
              ¬terminal.indexed.segment.start.1 <
                terminal.indexed.segment.finish.1 := by
            omega
          simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, horizontal', notForward,
            backward]
          cases terminal.endpoint <;> norm_num
      · rcases vertical with ⟨sameX, differentY⟩
        have notHorizontal :
            ¬terminal.indexed.segment.IsHorizontal := by
          intro horizontal
          exact differentY horizontal.1
        rcases lt_or_gt_of_ne differentY with forward | backward
        · simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, sameX, notHorizontal,
            forward]
          cases terminal.endpoint <;> norm_num
        · have notForward :
              ¬terminal.indexed.segment.start.2 <
                terminal.indexed.segment.finish.2 := by
            omega
          simp [CarrierNode.isHorizontal,
            CarrierNode.localPosition,
            segmentTerminalLocalPosition, sameX, notHorizontal,
            notForward, backward]
          cases terminal.endpoint <;> norm_num

/-- A point in a horizontal segment interior has the segment's fixed second
coordinate. -/
theorem GridSegment.snd_eq_start_of_interiorContains_horizontal
    {segment : GridSegment} {point : Cell}
    (contains : segment.InteriorContains point)
    (horizontal : segment.IsHorizontal) :
    point.2 = segment.start.2 := by
  rcases contains with onHorizontal | onVertical
  · exact onHorizontal.2.1
  · exact False.elim (onVertical.1.2 horizontal.1)

/-- A point in a vertical segment interior has the segment's fixed first
coordinate. -/
theorem GridSegment.fst_eq_start_of_interiorContains_vertical
    {segment : GridSegment} {point : Cell}
    (contains : segment.InteriorContains point)
    (vertical : segment.IsVertical) :
    point.1 = segment.start.1 := by
  rcases contains with onHorizontal | onVertical
  · exact False.elim (vertical.2 onHorizontal.1.1)
  · exact onVertical.2.1

/-- Two canonical crossings sharing their horizontal occurrence and crossing
point are the same complete crossing record. -/
theorem orientedCrossing_eq_of_firstOccurrence_eq_of_point_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossingHalo graph)
    (secondMem : second ∈ orientedCrossingHalo graph)
    (firstIndexedEqual : first.first = second.first)
    (firstTranslateEqual :
      first.firstTranslate = second.firstTranslate)
    (pointEqual : first.point = second.point) :
    first = second := by
  have firstSound := orientedCrossingHalo_sound graph firstMem
  have secondSound := orientedCrossingHalo_sound graph secondMem
  have secondKeyEqual :
      PeriodicGridDrawing.SegmentOccurrenceKey
          first.second first.secondTranslate =
        PeriodicGridDrawing.SegmentOccurrenceKey
          second.second second.secondTranslate := by
    by_contra keyDifferent
    have proper :=
      drawing_isOrthocrossing wellFormed degree isLocal
        first.second firstSound.2.1
        second.second secondSound.2.1
        first.secondTranslate second.secondTranslate first.point
        keyDifferent
        firstSound.2.2.2.2.2.2.2.2.1
        (by
          rw [pointEqual]
          exact secondSound.2.2.2.2.2.2.2.2.1)
    have firstVertical :=
      firstSound.2.2.2.2.2.2.1
    have secondVertical :=
      secondSound.2.2.2.2.2.2.1
    rcases proper.2.2 with horizontalVertical | verticalHorizontal
    · exact firstVertical.2 horizontalVertical.1.1
    · exact secondVertical.2 verticalHorizontal.2.1
  have secondIndexedEqual :
      first.second = second.second := by
    apply indexedSegment_eq_of_indices_eq (drawing graph)
      firstSound.2.1 secondSound.2.1
    · exact congrArg Prod.fst secondKeyEqual
    · exact congrArg (fun key => key.2.1) secondKeyEqual
  have secondTranslateEqual :
      first.secondTranslate = second.secondTranslate :=
    congrArg (fun key => key.2.2) secondKeyEqual
  cases first
  cases second
  congr

/-- Two canonical crossings sharing their vertical occurrence and crossing
point are the same complete crossing record. -/
theorem orientedCrossing_eq_of_secondOccurrence_eq_of_point_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossingHalo graph)
    (secondMem : second ∈ orientedCrossingHalo graph)
    (secondIndexedEqual : first.second = second.second)
    (secondTranslateEqual :
      first.secondTranslate = second.secondTranslate)
    (pointEqual : first.point = second.point) :
    first = second := by
  have firstSound := orientedCrossingHalo_sound graph firstMem
  have secondSound := orientedCrossingHalo_sound graph secondMem
  have firstKeyEqual :
      PeriodicGridDrawing.SegmentOccurrenceKey
          first.first first.firstTranslate =
        PeriodicGridDrawing.SegmentOccurrenceKey
          second.first second.firstTranslate := by
    by_contra keyDifferent
    have proper :=
      drawing_isOrthocrossing wellFormed degree isLocal
        first.first firstSound.1
        second.first secondSound.1
        first.firstTranslate second.firstTranslate first.point
        keyDifferent
        firstSound.2.2.2.2.2.2.2.1
        (by
          rw [pointEqual]
          exact secondSound.2.2.2.2.2.2.2.1)
    have firstHorizontal :=
      firstSound.2.2.2.2.2.1
    have secondHorizontal :=
      secondSound.2.2.2.2.2.1
    rcases proper.2.2 with horizontalVertical | verticalHorizontal
    · exact secondHorizontal.2 horizontalVertical.2.1
    · exact firstHorizontal.2 verticalHorizontal.1.1
  have firstIndexedEqual :
      first.first = second.first := by
    apply indexedSegment_eq_of_indices_eq (drawing graph)
      firstSound.1 secondSound.1
    · exact congrArg Prod.fst firstKeyEqual
    · exact congrArg (fun key => key.2.1) firstKeyEqual
  have firstTranslateEqual :
      first.firstTranslate = second.firstTranslate :=
    congrArg (fun key => key.2.2) firstKeyEqual
  cases first
  cases second
  congr

/-- Crossing points on one horizontal occurrence have the same second
coordinate. -/
theorem orientedCrossing_point_snd_eq_of_firstOccurrence_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossingHalo graph)
    (secondMem : second ∈ orientedCrossingHalo graph)
    (indexedEqual : first.first = second.first)
    (translateEqual :
      first.firstTranslate = second.firstTranslate) :
    first.point.2 = second.point.2 := by
  have firstSound := orientedCrossingHalo_sound graph firstMem
  have secondSound := orientedCrossingHalo_sound graph secondMem
  have firstCoordinate :=
    GridSegment.snd_eq_start_of_interiorContains_horizontal
      firstSound.2.2.2.2.2.2.2.1
      firstSound.2.2.2.2.2.1
  have secondCoordinate :=
    GridSegment.snd_eq_start_of_interiorContains_horizontal
      secondSound.2.2.2.2.2.2.2.1
      secondSound.2.2.2.2.2.1
  simp [CrossingRecord.firstSegment,
    indexedEqual, translateEqual] at firstCoordinate
  exact firstCoordinate.trans secondCoordinate.symm

/-- Crossing points on one vertical occurrence have the same first
coordinate. -/
theorem orientedCrossing_point_fst_eq_of_secondOccurrence_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossingHalo graph)
    (secondMem : second ∈ orientedCrossingHalo graph)
    (indexedEqual : first.second = second.second)
    (translateEqual :
      first.secondTranslate = second.secondTranslate) :
    first.point.1 = second.point.1 := by
  have firstSound := orientedCrossingHalo_sound graph firstMem
  have secondSound := orientedCrossingHalo_sound graph secondMem
  have firstCoordinate :=
    GridSegment.fst_eq_start_of_interiorContains_vertical
      firstSound.2.2.2.2.2.2.2.2.1
      firstSound.2.2.2.2.2.2.1
  have secondCoordinate :=
    GridSegment.fst_eq_start_of_interiorContains_vertical
      secondSound.2.2.2.2.2.2.2.2.1
      secondSound.2.2.2.2.2.2.1
  simp [CrossingRecord.secondSegment,
    indexedEqual, translateEqual] at firstCoordinate
  exact firstCoordinate.trans secondCoordinate.symm

/-- Distinct crossover sites on one carrier never share the same refined
order coordinate. -/
theorem crossingBoundary_orderCoordinate_ne_of_common_carrier
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingBoundary}
    (firstMem : first ∈ drawingCrossingBoundaries graph)
    (secondMem : second ∈ drawingCrossingBoundaries graph)
    (keyEqual : first.carrierKey = second.carrierKey)
    (crossingDifferent : first.crossing ≠ second.crossing) :
    (CarrierNode.boundary first).orderCoordinate graph ≠
      (CarrierNode.boundary second).orderCoordinate graph := by
  have firstNodeMem :
      CarrierNode.boundary first ∈ drawingCarrierNodes graph := by
    unfold drawingCarrierNodes
    simp [firstMem]
  have secondNodeMem :
      CarrierNode.boundary second ∈ drawingCarrierNodes graph := by
    unfold drawingCarrierNodes
    simp [secondMem]
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph firstNodeMem secondNodeMem keyEqual
  have firstCrossingMem :=
    drawingCrossingBoundary_crossing_mem graph firstMem
  have secondCrossingMem :=
    drawingCrossingBoundary_crossing_mem graph secondMem
  have firstSound :=
    orientedCrossingHalo_sound graph firstCrossingMem
  have secondSound :=
    orientedCrossingHalo_sound graph secondCrossingMem
  intro coordinateEqual
  cases first with
  | mk firstCrossing firstSide =>
      cases second with
      | mk secondCrossing secondSide =>
          cases firstSide <;> cases secondSide
          · have pointSndEqual :=
              orientedCrossing_point_snd_eq_of_firstOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointFstEqual :
                firstCrossing.point.1 =
                  secondCrossing.point.1 := by
              change
                20 * firstCrossing.point.1 + 1 =
                  20 * secondCrossing.point.1 + 1
                at coordinateEqual
              omega
            exact crossingDifferent
              (orientedCrossing_eq_of_firstOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))
          · change
              20 * firstCrossing.point.1 + 1 =
                20 * secondCrossing.point.1 + 11
              at coordinateEqual
            omega
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                firstSound.2.2.2.2.2.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp
                secondSound.2.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                firstSound.2.2.2.2.2.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp
                secondSound.2.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · change
              20 * firstCrossing.point.1 + 11 =
                20 * secondCrossing.point.1 + 1
              at coordinateEqual
            omega
          · have pointSndEqual :=
              orientedCrossing_point_snd_eq_of_firstOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointFstEqual :
                firstCrossing.point.1 =
                  secondCrossing.point.1 := by
              change
                20 * firstCrossing.point.1 + 11 =
                  20 * secondCrossing.point.1 + 11
                at coordinateEqual
              omega
            exact crossingDifferent
              (orientedCrossing_eq_of_firstOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                firstSound.2.2.2.2.2.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp
                secondSound.2.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · have firstHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                firstSound.2.2.2.2.2.1
            have secondVertical :=
              (GridSegment.isVertical_translate _ _).mp
                secondSound.2.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstHorizontal
            exact secondVertical.2 firstHorizontal.1
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp
                firstSound.2.2.2.2.2.2.1
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                secondSound.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp
                firstSound.2.2.2.2.2.2.1
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                secondSound.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · have pointFstEqual :=
              orientedCrossing_point_fst_eq_of_secondOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointSndEqual :
                firstCrossing.point.2 =
                  secondCrossing.point.2 := by
              change
                20 * firstCrossing.point.2 + 1 =
                  20 * secondCrossing.point.2 + 1
                at coordinateEqual
              omega
            exact crossingDifferent
              (orientedCrossing_eq_of_secondOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))
          · change
              20 * firstCrossing.point.2 + 1 =
                20 * secondCrossing.point.2 + 11
              at coordinateEqual
            omega
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp
                firstSound.2.2.2.2.2.2.1
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                secondSound.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · have firstVertical :=
              (GridSegment.isVertical_translate _ _).mp
                firstSound.2.2.2.2.2.2.1
            have secondHorizontal :=
              (GridSegment.isHorizontal_translate _ _).mp
                secondSound.2.2.2.2.2.1
            simp [CarrierNode.indexed,
              CrossingBoundary.indexed] at occurrenceEqual
            rw [occurrenceEqual.1] at firstVertical
            exact firstVertical.2 secondHorizontal.1
          · change
              20 * firstCrossing.point.2 + 11 =
                20 * secondCrossing.point.2 + 1
              at coordinateEqual
            omega
          · have pointFstEqual :=
              orientedCrossing_point_fst_eq_of_secondOccurrence_eq
                graph firstCrossingMem secondCrossingMem
                  occurrenceEqual.1 occurrenceEqual.2
            have pointSndEqual :
                firstCrossing.point.2 =
                  secondCrossing.point.2 := by
              change
                20 * firstCrossing.point.2 + 11 =
                  20 * secondCrossing.point.2 + 11
                at coordinateEqual
              omega
            exact crossingDifferent
              (orientedCrossing_eq_of_secondOccurrence_eq_of_point_eq
                wellFormed degree isLocal
                firstCrossingMem secondCrossingMem
                occurrenceEqual.1 occurrenceEqual.2
                (Prod.ext pointFstEqual pointSndEqual))

/-- Nodes with one occurrence key lie on one refined axis.  Their axial
coordinates all occupy the residue class `1 mod 10`, which later turns
strict sorted order into a ten-cell gap. -/
theorem carrierNode_commonCarrier_axis_data
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ drawingCarrierNodes graph)
    (secondMem : second ∈ drawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey) :
    if first.isHorizontal then
      (first.position graph).2 = (second.position graph).2 ∧
        (first.position graph).1 % 10 = 1 ∧
        (second.position graph).1 % 10 = 1
    else
      (first.position graph).1 = (second.position graph).1 ∧
        (first.position graph).2 % 10 = 1 ∧
        (second.position graph).2 % 10 = 1 := by
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph firstMem secondMem keyEqual
  have firstAligned :
      first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      first.indexed (carrierNode_indexed_mem graph firstMem)
  have secondAligned :
      second.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  have firstContains :=
    carrierNode_drawingPoint_contains
      graph firstMem firstAligned
  have secondContains :=
    carrierNode_drawingPoint_contains
      graph secondMem secondAligned
  have firstLocal :=
    carrierNode_localPosition_axis_data
      graph firstMem firstAligned
  have secondLocal :=
    carrierNode_localPosition_axis_data
      graph secondMem secondAligned
  by_cases horizontalTag : first.isHorizontal = true
  · rw [if_pos horizontalTag]
    have firstHorizontal :
        first.indexed.segment.IsHorizontal :=
      (carrierNode_isHorizontal_iff
        graph firstMem firstAligned).mp horizontalTag
    have secondHorizontal :
        second.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    have secondHorizontalTag :
        second.isHorizontal = true :=
      (carrierNode_isHorizontal_iff
        graph secondMem secondAligned).mpr secondHorizontal
    rw [if_pos horizontalTag] at firstLocal
    rw [if_pos secondHorizontalTag] at secondLocal
    let segment :=
      first.indexed.segment.translate
        ((drawing graph).periodTranslation first.translate)
    have segmentHorizontal : segment.IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr firstHorizontal
    have secondSegmentEqual :
        second.indexed.segment.translate
            ((drawing graph).periodTranslation second.translate) =
          segment := by
      simp [segment, occurrenceEqual.1, occurrenceEqual.2]
    rw [secondSegmentEqual] at secondContains
    have firstY :
        (first.drawingPoint graph).2 = segment.start.2 := by
      rcases firstContains with horizontal | vertical
      · exact horizontal.2.1
      · exact False.elim (vertical.1.2 segmentHorizontal.1)
    have secondY :
        (second.drawingPoint graph).2 = segment.start.2 := by
      rcases secondContains with horizontal | vertical
      · exact horizontal.2.1
      · exact False.elim (vertical.1.2 segmentHorizontal.1)
    rw [CarrierNode.position_eq_scale_add_local,
      CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega
  · have firstNotHorizontal :
        ¬first.indexed.segment.IsHorizontal := by
      intro horizontal
      exact horizontalTag
        ((carrierNode_isHorizontal_iff
          graph firstMem firstAligned).mpr horizontal)
    have firstVertical :
        first.indexed.segment.IsVertical :=
      firstAligned.resolve_left firstNotHorizontal
    have secondVertical :
        second.indexed.segment.IsVertical := by
      rw [← occurrenceEqual.1]
      exact firstVertical
    have secondNotHorizontal :
        ¬second.indexed.segment.IsHorizontal := by
      intro horizontal
      exact secondVertical.2 horizontal.1
    have secondHorizontalTag :
        second.isHorizontal = false := by
      apply Bool.eq_false_iff.mpr
      intro tag
      exact secondNotHorizontal
        ((carrierNode_isHorizontal_iff
          graph secondMem secondAligned).mp tag)
    rw [if_neg horizontalTag]
    rw [if_neg horizontalTag] at firstLocal
    rw [if_neg (by simpa using secondHorizontalTag)] at secondLocal
    let segment :=
      first.indexed.segment.translate
        ((drawing graph).periodTranslation first.translate)
    have segmentVertical : segment.IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr firstVertical
    have secondSegmentEqual :
        second.indexed.segment.translate
            ((drawing graph).periodTranslation second.translate) =
          segment := by
      simp [segment, occurrenceEqual.1, occurrenceEqual.2]
    rw [secondSegmentEqual] at secondContains
    have firstX :
        (first.drawingPoint graph).1 = segment.start.1 := by
      rcases firstContains with horizontal | vertical
      · exact False.elim (segmentVertical.2 horizontal.1.1)
      · exact vertical.2.1
    have secondX :
        (second.drawingPoint graph).1 = segment.start.1 := by
      rcases secondContains with horizontal | vertical
      · exact False.elim (segmentVertical.2 horizontal.1.1)
      · exact vertical.2.1
    rw [CarrierNode.position_eq_scale_add_local,
      CarrierNode.position_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, planarMacroScale]
    omega

/-- Every retained adjacent pair in a complete carrier is strictly ordered
by its physical axis coordinate. -/
theorem completeCarrierPair_orderCoordinate_lt
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell)
    {pair : CarrierNode × CarrierNode}
    (pairMem :
      pair ∈ consecutivePairs (completeCarrierNodes graph key))
    (retained :
      !pair.1.sameCrossoverSite pair.2) :
    pair.1.orderCoordinate graph <
      pair.2.orderCoordinate graph := by
  have members := mem_of_mem_consecutivePairs pairMem
  have firstData :=
    (mem_completeCarrierNodes_iff graph key pair.1).mp members.1
  have secondData :=
    (mem_completeCarrierNodes_iff graph key pair.2).mp members.2
  have different :=
    consecutivePairs_ne_of_nodup
      (completeCarrierNodes_nodup graph key) pairMem
  have sorted :
      (completeCarrierNodes graph key).Pairwise
        fun first second =>
          first.orderCoordinate graph ≤
            second.orderCoordinate graph := by
    unfold completeCarrierNodes
    exact List.pairwise_insertionSort _ _
  have ordered :=
    consecutivePairs_rel_of_pairwise sorted pairMem
  cases firstNodeEqual : pair.1 with
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        rw [firstNodeEqual] at firstData
        unfold drawingCarrierNodes at firstData
        simpa using firstData.1
      have keyEqual :
          pair.2.carrierKey = terminal.carrierKey := by
        rw [firstNodeEqual] at firstData
        exact secondData.2.trans firstData.2.symm
      have secondDifferent :
          pair.2 ≠ CarrierNode.terminal terminal := by
        rw [← firstNodeEqual]
        exact different.symm
      have extreme :=
        carrierNode_terminal_extreme
          wellFormed degree isLocal terminalMem
          secondData.1 keyEqual secondDifferent
      by_cases lower : terminal.IsLower
      · rw [if_pos lower] at extreme
        simpa [firstNodeEqual] using extreme
      · rw [if_neg lower] at extreme
        rw [firstNodeEqual] at ordered
        omega
  | boundary firstBoundary =>
      cases secondNodeEqual : pair.2 with
      | terminal terminal =>
          have terminalMem :
              terminal ∈ drawingSegmentTerminals graph := by
            rw [secondNodeEqual] at secondData
            unfold drawingCarrierNodes at secondData
            simpa using secondData.1
          have keyEqual :
              pair.1.carrierKey = terminal.carrierKey := by
            rw [secondNodeEqual] at secondData
            exact firstData.2.trans secondData.2.symm
          have firstDifferent :
              pair.1 ≠ CarrierNode.terminal terminal := by
            rw [← secondNodeEqual]
            exact different
          have extreme :=
            carrierNode_terminal_extreme
              wellFormed degree isLocal terminalMem
              firstData.1 keyEqual firstDifferent
          by_cases lower : terminal.IsLower
          · rw [if_pos lower] at extreme
            rw [secondNodeEqual] at ordered
            omega
          · rw [if_neg lower] at extreme
            rw [firstNodeEqual] at extreme
            simpa [secondNodeEqual] using extreme
      | boundary secondBoundary =>
          have firstBoundaryMem :
              firstBoundary ∈ drawingCrossingBoundaries graph := by
            rw [firstNodeEqual] at firstData
            unfold drawingCarrierNodes at firstData
            simpa using firstData.1
          have secondBoundaryMem :
              secondBoundary ∈ drawingCrossingBoundaries graph := by
            rw [secondNodeEqual] at secondData
            unfold drawingCarrierNodes at secondData
            simpa using secondData.1
          have boundaryKeyEqual :
              firstBoundary.carrierKey =
                secondBoundary.carrierKey := by
            rw [firstNodeEqual] at firstData
            rw [secondNodeEqual] at secondData
            exact firstData.2.trans secondData.2.symm
          have crossingDifferent :
              firstBoundary.crossing ≠
                secondBoundary.crossing := by
            intro crossingEqual
            rw [firstNodeEqual, secondNodeEqual] at retained
            simp [CarrierNode.sameCrossoverSite,
              crossingEqual] at retained
          have coordinateDifferent :=
            crossingBoundary_orderCoordinate_ne_of_common_carrier
              wellFormed degree isLocal
              firstBoundaryMem secondBoundaryMem
              boundaryKeyEqual crossingDifferent
          rw [firstNodeEqual, secondNodeEqual] at ordered
          omega

/-- Two carrier nodes advance by at least eight refined cells along the
axis selected by the first node. -/
def CarrierNode.HasForwardClearance
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : CarrierNode) : Prop :=
  if first.isHorizontal then
    (first.position graph).2 = (second.position graph).2 ∧
      (first.position graph).1 + 8 ≤ (second.position graph).1
  else
    (first.position graph).1 = (second.position graph).1 ∧
      (first.position graph).2 + 8 ≤ (second.position graph).2

/-- Every retained complete-carrier pair has enough physical clearance for
the eight-cell equality lens. -/
theorem completeCarrierPair_hasForwardClearance
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell)
    {pair : CarrierNode × CarrierNode}
    (pairMem :
      pair ∈ consecutivePairs (completeCarrierNodes graph key))
    (retained :
      !pair.1.sameCrossoverSite pair.2) :
    pair.1.HasForwardClearance graph pair.2 := by
  have members := mem_of_mem_consecutivePairs pairMem
  have firstData :=
    (mem_completeCarrierNodes_iff graph key pair.1).mp members.1
  have secondData :=
    (mem_completeCarrierNodes_iff graph key pair.2).mp members.2
  have keyEqual :
      pair.1.carrierKey = pair.2.carrierKey :=
    firstData.2.trans secondData.2.symm
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph firstData.1 secondData.1 keyEqual
  have firstAligned :
      pair.1.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      pair.1.indexed
      (carrierNode_indexed_mem graph firstData.1)
  have secondAligned :
      pair.2.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  have axisData :=
    carrierNode_commonCarrier_axis_data
      wellFormed degree isLocal
      firstData.1 secondData.1 keyEqual
  have strict :=
    completeCarrierPair_orderCoordinate_lt
      wellFormed degree isLocal key pairMem retained
  unfold CarrierNode.HasForwardClearance
  by_cases horizontal : pair.1.isHorizontal = true
  · rw [if_pos horizontal]
    have firstHorizontal :
        pair.1.indexed.segment.IsHorizontal :=
      (carrierNode_isHorizontal_iff
        graph firstData.1 firstAligned).mp horizontal
    have secondHorizontal :
        pair.2.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    have secondHorizontalTag :
        pair.2.isHorizontal = true :=
      (carrierNode_isHorizontal_iff
        graph secondData.1 secondAligned).mpr secondHorizontal
    have axisData' :
        (pair.1.position graph).2 =
            (pair.2.position graph).2 ∧
          (pair.1.position graph).1 % 10 = 1 ∧
          (pair.2.position graph).1 % 10 = 1 := by
      simpa [horizontal] using axisData
    have strict' :
        (pair.1.position graph).1 <
          (pair.2.position graph).1 := by
      simpa [CarrierNode.orderCoordinate,
        horizontal, secondHorizontalTag] using strict
    omega
  · rw [if_neg horizontal]
    have secondNotHorizontalTag :
        ¬pair.2.isHorizontal = true := by
      intro secondHorizontalTag
      have secondHorizontal :=
        (carrierNode_isHorizontal_iff
          graph secondData.1 secondAligned).mp secondHorizontalTag
      have firstHorizontal :
          pair.1.indexed.segment.IsHorizontal := by
        rw [occurrenceEqual.1]
        exact secondHorizontal
      exact horizontal
        ((carrierNode_isHorizontal_iff
          graph firstData.1 firstAligned).mpr firstHorizontal)
    have axisData' :
        (pair.1.position graph).1 =
            (pair.2.position graph).1 ∧
          (pair.1.position graph).2 % 10 = 1 ∧
          (pair.2.position graph).2 % 10 = 1 := by
      simpa [horizontal] using axisData
    have strict' :
        (pair.1.position graph).2 <
          (pair.2.position graph).2 := by
      simpa [CarrierNode.orderCoordinate,
        horizontal, secondNotHorizontalTag] using strict
    omega

/-- Forward clearance is exactly the input-specific fact needed to turn a
complete-carrier pair into a certified equality lens. -/
theorem carrierNodePairLink_lensGeometry_of_hasForwardClearance
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : CarrierNode × CarrierNode)
    (different : pair.1 ≠ pair.2)
    (clearance : pair.1.HasForwardClearance graph pair.2) :
    EqualityLink.LensGeometry
      (CarrierNode.position graph)
      (carrierNodePairLink graph pair) := by
  simp only [carrierNodePairLink]
  refine
    { different := different
      axisAligned := ?_
      spanLarge := ?_
      positions := ?_ }
  · unfold CarrierNode.HasForwardClearance at clearance
    split at clearance
    · apply Or.inl
      refine ⟨clearance.1, ?_⟩
      intro coordinateEqual
      change (pair.1.position graph).1 =
        (pair.2.position graph).1 at coordinateEqual
      omega
    · apply Or.inr
      refine ⟨clearance.1, ?_⟩
      intro coordinateEqual
      change (pair.1.position graph).2 =
        (pair.2.position graph).2 at coordinateEqual
      omega
  · unfold CarrierNode.HasForwardClearance at clearance
    simp only [AxisDirection.axisSpan]
    split at clearance
    · rw [abs_of_nonneg (by omega : 0 ≤
        (pair.2.position graph).1 - (pair.1.position graph).1)]
      simp [clearance.1]
      omega
    · rw [abs_of_nonneg (by omega : 0 ≤
        (pair.2.position graph).2 - (pair.1.position graph).2)]
      simp [clearance.1]
      omega
  · unfold CarrierNode.HasForwardClearance at clearance
    split at clearance
    · have xLt :
          (pair.1.position graph).1 <
            (pair.2.position graph).1 := by
        omega
      have xLe :
          (pair.1.position graph).1 ≤
            (pair.2.position graph).1 := xLt.le
      simp_all [carrierNodeEqualityPositions,
        AxisDirection.between,
        AxisDirection.placePoint, AxisDirection.orientPoint,
        Cell.add]
    · have yLt :
          (pair.1.position graph).2 <
            (pair.2.position graph).2 := by
        omega
      have yNe :
          (pair.1.position graph).2 ≠
            (pair.2.position graph).2 := by
        omega
      have yLe :
          (pair.1.position graph).2 ≤
            (pair.2.position graph).2 := yLt.le
      simp_all [carrierNodeEqualityPositions,
        AxisDirection.between,
        AxisDirection.placePoint, AxisDirection.orientPoint,
        Cell.add]

/-- Every retained complete-carrier equality link satisfies the generic
equality-lens geometry interface. -/
theorem completeCarrierLink_lensGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ completeCarrierLinks graph key) :
    EqualityLink.LensGeometry
      (CarrierNode.position graph) link := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  apply
    carrierNodePairLink_lensGeometry_of_hasForwardClearance
      graph pair
  · exact consecutivePairs_ne_of_nodup
      (completeCarrierNodes_nodup graph key) pairData.1
  · exact completeCarrierPair_hasForwardClearance
      wellFormed degree isLocal key pairData.1 pairData.2

/-- The aggregate complete-carrier family inherits the certified geometry
of its individual chain links. -/
theorem drawingCompleteCarrierLink_lensGeometry
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    EqualityLink.LensGeometry
      (CarrierNode.position graph) link := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, linkMem⟩
  exact completeCarrierLink_lensGeometry
    wellFormed degree isLocal key linkMem

/-- Each aggregate complete-carrier lens draws exactly its source equality
instance. -/
theorem drawingCompleteCarrierLink_lensDrawing_formula
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).formula =
        equalityInstance link.first link.second link.positions :=
  EqualityLink.lensDrawing_formula
    (drawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

/-- Each aggregate complete-carrier lens recovers the assigned position of
its first endpoint. -/
theorem drawingCompleteCarrierLink_lensDrawing_firstPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).variablePosition link.first =
        link.first.position graph :=
  EqualityLink.lensDrawing_firstPosition
    (drawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

/-- Each aggregate complete-carrier lens recovers the assigned position of
its second endpoint. -/
theorem drawingCompleteCarrierLink_lensDrawing_secondPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).variablePosition link.second =
        link.second.position graph :=
  EqualityLink.lensDrawing_secondPosition
    (drawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

/-- Every aggregate complete-carrier lens has exact endpoints, orthogonal
routes, and continuous finite planarity. -/
theorem drawingCompleteCarrierLink_lensDrawing_isValid
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    (EqualityLink.lensDrawing
      (CarrierNode.position graph) link).IsValid :=
  EqualityLink.lensDrawing_isValid
    (drawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem)

end PeriodicOrthocrossing
end LeanTrominoes

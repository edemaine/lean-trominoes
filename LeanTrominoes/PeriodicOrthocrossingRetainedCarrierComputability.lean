/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierEncodingComputability
import LeanTrominoes.PrimrecListSort

/-!
# Computability of retained carrier chains

The bounded crossing orbit, segment terminals, physical carrier nodes, and
their sorted per-carrier chains are primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

theorem CrossingRecord.periodTranslate_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input :
        (PeriodicGraph Vertex × CrossingRecord) × Cell =>
      input.1.2.periodTranslate input.1.1 input.2 := by
  have graph : Primrec fun input :
      (PeriodicGraph Vertex × CrossingRecord) × Cell => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have record : Primrec fun input :
      (PeriodicGraph Vertex × CrossingRecord) × Cell => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have firstTranslate : Primrec fun input :
      (PeriodicGraph Vertex × CrossingRecord) × Cell =>
      Cell.add input.1.2.firstTranslate input.2 :=
    Computability.cell_add_primrec.comp
      (CrossingRecord.firstTranslate_primrec.comp record) Primrec.snd
  have secondTranslate : Primrec fun input :
      (PeriodicGraph Vertex × CrossingRecord) × Cell =>
      Cell.add input.1.2.secondTranslate input.2 :=
    Computability.cell_add_primrec.comp
      (CrossingRecord.secondTranslate_primrec.comp record) Primrec.snd
  have translation : Primrec fun input :
      (PeriodicGraph Vertex × CrossingRecord) × Cell =>
      (drawing input.1.1).periodTranslation input.2 :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      (drawing_primrec.comp graph) Primrec.snd
  have point : Primrec fun input :
      (PeriodicGraph Vertex × CrossingRecord) × Cell =>
      Cell.add input.1.2.point
        ((drawing input.1.1).periodTranslation input.2) :=
    Computability.cell_add_primrec.comp
      (CrossingRecord.point_primrec.comp record) translation
  exact (CrossingRecord.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (CrossingRecord.first_primrec.comp record) firstTranslate)
      (Primrec.pair
        (Primrec.pair
          (CrossingRecord.second_primrec.comp record) secondTranslate)
        point))).of_eq fun _ => rfl

theorem retainedCrossings_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedCrossings :
      PeriodicGraph Vertex → List CrossingRecord) := by
  have translated : Primrec₂ fun (graph : PeriodicGraph Vertex)
      (crossing : CrossingRecord) =>
      carrierCrossingRetentionShifts.map fun shift =>
        crossing.periodTranslate graph shift := by
    change Primrec fun input : PeriodicGraph Vertex × CrossingRecord =>
      carrierCrossingRetentionShifts.map fun shift =>
        input.2.periodTranslate input.1 shift
    exact Primrec.list_map
      (Primrec.const carrierCrossingRetentionShifts)
      (CrossingRecord.periodTranslate_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.snd.comp Primrec.fst))
          Primrec.snd)).to₂
  exact (Primrec.list_flatMap orientedCrossings_primrec translated).of_eq
    fun _ => rfl

theorem retainedCrossingBoundaries_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedCrossingBoundaries :
      PeriodicGraph Vertex → List CrossingBoundary) := by
  have boundaries : Primrec fun crossing : CrossingRecord =>
      [CrossingBoundary.mk crossing .left,
        CrossingBoundary.mk crossing .right,
        CrossingBoundary.mk crossing .top,
        CrossingBoundary.mk crossing .bottom] := by
    let boundary (side : CrossingSide) :
        Primrec fun crossing : CrossingRecord =>
        CrossingBoundary.equivData.symm (crossing, side) :=
      CrossingBoundary.equivData_symm_primrec.comp
        (Primrec.pair Primrec.id (Primrec.const side))
    exact (Primrec.list_cons.comp (boundary .left)
      (Primrec.list_cons.comp (boundary .right)
        (Primrec.list_cons.comp (boundary .top)
          (Primrec.list_cons.comp (boundary .bottom)
            (Primrec.const []))))).of_eq fun _ => rfl
  exact Primrec.list_flatMap retainedCrossings_primrec
    (boundaries.comp₂ Primrec₂.right)

theorem occurrenceTerminals_primrec :
    Primrec occurrenceTerminals := by
  let terminal (endpoint : SegmentEnd) : Primrec fun occurrence :
      IndexedGridSegment × Cell =>
      SegmentTerminal.mk occurrence.1 occurrence.2 endpoint :=
    SegmentTerminal.mk_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const endpoint))
  exact Primrec.list_cons.comp (terminal .start)
    (Primrec.list_cons.comp (terminal .finish) (Primrec.const []))

theorem drawingSegmentTerminals_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingSegmentTerminals :
      PeriodicGraph Vertex → List SegmentTerminal) :=
  Primrec.list_flatMap neighborOccurrences_primrec
    (occurrenceTerminals_primrec.comp₂ Primrec₂.right)

theorem retainedDrawingCarrierNodes_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingCarrierNodes :
      PeriodicGraph Vertex → List CarrierNode) := by
  have terminals : Primrec fun graph : PeriodicGraph Vertex =>
      (drawingSegmentTerminals graph).map CarrierNode.terminal :=
    Primrec.list_map drawingSegmentTerminals_primrec
      (CarrierNode.terminal_primrec.comp₂ Primrec₂.right)
  have boundaries : Primrec fun graph : PeriodicGraph Vertex =>
      (retainedCrossingBoundaries graph).map CarrierNode.boundary :=
    Primrec.list_map retainedCrossingBoundaries_primrec
      (CarrierNode.boundary_primrec.comp₂ Primrec₂.right)
  exact Primrec.list_append.comp terminals boundaries

theorem SegmentTerminal.carrierKey_primrec :
    Primrec SegmentTerminal.carrierKey :=
  PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
    SegmentTerminal.indexed_primrec SegmentTerminal.translate_primrec

theorem CrossingBoundary.carrierKey_primrec :
    Primrec CrossingBoundary.carrierKey := by
  have crossing := CrossingBoundary.crossing_primrec
  have side := CrossingBoundary.side_primrec
  have horizontal : PrimrecPred fun boundary : CrossingBoundary =>
      boundary.side = .left ∨ boundary.side = .right :=
    (Primrec.eq.comp side (Primrec.const CrossingSide.left)).or
      (Primrec.eq.comp side (Primrec.const CrossingSide.right))
  have first : Primrec fun boundary : CrossingBoundary =>
      PeriodicGridDrawing.SegmentOccurrenceKey
        boundary.crossing.first boundary.crossing.firstTranslate :=
    PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
      (CrossingRecord.first_primrec.comp crossing)
      (CrossingRecord.firstTranslate_primrec.comp crossing)
  have second : Primrec fun boundary : CrossingBoundary =>
      PeriodicGridDrawing.SegmentOccurrenceKey
        boundary.crossing.second boundary.crossing.secondTranslate :=
    PeriodicGridDrawing.segmentOccurrenceKey_primrec.comp
      (CrossingRecord.second_primrec.comp crossing)
      (CrossingRecord.secondTranslate_primrec.comp crossing)
  exact (Primrec.ite horizontal first second).of_eq fun boundary => by
    rcases boundary with ⟨crossing, side⟩
    cases side <;> rfl

theorem CarrierNode.carrierKey_primrec :
    Primrec CarrierNode.carrierKey := by
  exact (Primrec.sumCasesOn CarrierNode.equivData_primrec
    (CrossingBoundary.carrierKey_primrec.comp₂ Primrec₂.right)
    (SegmentTerminal.carrierKey_primrec.comp₂ Primrec₂.right)).of_eq
      fun node => by cases node <;> rfl

theorem segmentTerminalLocalPosition_primrec :
    Primrec₂ segmentTerminalLocalPosition := by
  change Primrec fun input : GridSegment × SegmentEnd =>
    segmentTerminalLocalPosition input.1 input.2
  have startX : Primrec fun input : GridSegment × SegmentEnd =>
      input.1.start.1 :=
    (Primrec.fst.comp GridSegment.start_primrec).comp Primrec.fst
  have startY : Primrec fun input : GridSegment × SegmentEnd =>
      input.1.start.2 :=
    (Primrec.snd.comp GridSegment.start_primrec).comp Primrec.fst
  have finishX : Primrec fun input : GridSegment × SegmentEnd =>
      input.1.finish.1 :=
    (Primrec.fst.comp GridSegment.finish_primrec).comp Primrec.fst
  have finishY : Primrec fun input : GridSegment × SegmentEnd =>
      input.1.finish.2 :=
    (Primrec.snd.comp GridSegment.finish_primrec).comp Primrec.fst
  have east := Computability.int_lt_primrec.comp startX finishX
  have west := Computability.int_lt_primrec.comp finishX startX
  have north := Computability.int_lt_primrec.comp startY finishY
  have south := Computability.int_lt_primrec.comp finishY startY
  have isStart : PrimrecPred fun input : GridSegment × SegmentEnd =>
      input.2 = .start :=
    Primrec.eq.comp Primrec.snd (Primrec.const SegmentEnd.start)
  have choose (start finish : Cell) : Primrec fun input :
      GridSegment × SegmentEnd =>
      if input.2 = .start then start else finish :=
    Primrec.ite isStart (Primrec.const start) (Primrec.const finish)
  exact (Primrec.ite east (choose (11, 6) (1, 6))
    (Primrec.ite west (choose (1, 6) (11, 6))
      (Primrec.ite north (choose (6, 11) (6, 1))
        (Primrec.ite south (choose (6, 1) (6, 11))
          (Primrec.const (6, 6)))))).of_eq fun input => by
            rcases input with ⟨segment, endpoint⟩
            cases endpoint <;> simp [segmentTerminalLocalPosition]

theorem SegmentTerminal.drawingPoint_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (SegmentTerminal.drawingPoint :
      PeriodicGraph Vertex → SegmentTerminal → Cell) := by
  change Primrec fun input : PeriodicGraph Vertex × SegmentTerminal =>
    input.2.drawingPoint input.1
  have translated : Primrec fun input :
      PeriodicGraph Vertex × SegmentTerminal => GridSegment.translate
        ((drawing input.1).periodTranslation input.2.translate)
        input.2.indexed.segment :=
    GridSegment.translate_primrec.comp
      (PeriodicGridDrawing.periodTranslation_primrec.comp
        (drawing_primrec.comp Primrec.fst)
        (SegmentTerminal.translate_primrec.comp Primrec.snd))
      (IndexedGridSegment.segment_primrec.comp
        (SegmentTerminal.indexed_primrec.comp Primrec.snd))
  have isStart : PrimrecPred fun input :
      PeriodicGraph Vertex × SegmentTerminal =>
      input.2.endpoint = .start :=
    Primrec.eq.comp
      (SegmentTerminal.endpoint_primrec.comp Primrec.snd)
      (Primrec.const SegmentEnd.start)
  exact (Primrec.ite isStart
    (GridSegment.start_primrec.comp translated)
    (GridSegment.finish_primrec.comp translated)).of_eq fun input => by
      rcases input with ⟨graph, ⟨indexed, translate, endpoint⟩⟩
      cases endpoint <;> rfl

theorem SegmentTerminal.position_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (SegmentTerminal.position :
      PeriodicGraph Vertex → SegmentTerminal → Cell) := by
  change Primrec fun input : PeriodicGraph Vertex × SegmentTerminal =>
    input.2.position input.1
  have drawingPoint : Primrec fun input :
      PeriodicGraph Vertex × SegmentTerminal =>
      input.2.drawingPoint input.1 :=
    SegmentTerminal.drawingPoint_primrec
  have scaled : Primrec fun input :
      PeriodicGraph Vertex × SegmentTerminal =>
      Cell.scale planarMacroScale (input.2.drawingPoint input.1) :=
    Computability.cell_scale_primrec.comp
      (Primrec.const planarMacroScale) drawingPoint
  have localPosition : Primrec fun input :
      PeriodicGraph Vertex × SegmentTerminal =>
      segmentTerminalLocalPosition input.2.indexed.segment
        input.2.endpoint :=
    segmentTerminalLocalPosition_primrec.comp
      (IndexedGridSegment.segment_primrec.comp
        (SegmentTerminal.indexed_primrec.comp Primrec.snd))
      (SegmentTerminal.endpoint_primrec.comp Primrec.snd)
  exact Computability.cell_add_primrec.comp scaled localPosition

theorem CrossingSide.localPosition_primrec :
    Primrec CrossingSide.localPosition := by
  have is (side : CrossingSide) : PrimrecPred fun input : CrossingSide =>
      input = side := Primrec.eq.comp Primrec.id (Primrec.const side)
  exact (Primrec.ite (is .left)
    (Primrec.const (PlanarThreeSAT.CrossoverVariable.position .aLeft))
    (Primrec.ite (is .right)
      (Primrec.const (PlanarThreeSAT.CrossoverVariable.position .aRight))
      (Primrec.ite (is .top)
        (Primrec.const (PlanarThreeSAT.CrossoverVariable.position .bTop))
        (Primrec.const (PlanarThreeSAT.CrossoverVariable.position .bBottom))))).of_eq
          fun side => by cases side <;> rfl

theorem crossingMacroOrigin_primrec :
    Primrec crossingMacroOrigin :=
  Computability.cell_scale_primrec.comp
    (Primrec.const planarMacroScale) CrossingRecord.point_primrec

theorem CrossingBoundary.position_primrec :
    Primrec CrossingBoundary.position :=
  Computability.cell_add_primrec.comp
    (crossingMacroOrigin_primrec.comp CrossingBoundary.crossing_primrec)
    (CrossingSide.localPosition_primrec.comp CrossingBoundary.side_primrec)

theorem CarrierNode.position_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (CarrierNode.position :
      PeriodicGraph Vertex → CarrierNode → Cell) := by
  change Primrec fun input : PeriodicGraph Vertex × CarrierNode =>
    input.2.position input.1
  have data : Primrec fun input : PeriodicGraph Vertex × CarrierNode =>
      CarrierNode.equivData input.2 :=
    CarrierNode.equivData_primrec.comp Primrec.snd
  exact (Primrec.sumCasesOn data
    (CrossingBoundary.position_primrec.comp₂ Primrec₂.right)
    (SegmentTerminal.position_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).of_eq
        fun input => by cases input.2 <;> rfl

theorem CarrierNode.isHorizontal_primrec :
    Primrec CarrierNode.isHorizontal := by
  have boundary : Primrec fun boundary : CrossingBoundary =>
      decide (boundary.side = .left ∨ boundary.side = .right) :=
    ((Primrec.eq.comp CrossingBoundary.side_primrec
      (Primrec.const CrossingSide.left)).or
      (Primrec.eq.comp CrossingBoundary.side_primrec
        (Primrec.const CrossingSide.right))).decide
  have terminal : Primrec fun terminal : SegmentTerminal =>
      decide terminal.indexed.segment.IsHorizontal :=
    GridSegment.isHorizontal_primrec.decide.comp
      (IndexedGridSegment.segment_primrec.comp
        SegmentTerminal.indexed_primrec)
  exact (Primrec.sumCasesOn CarrierNode.equivData_primrec
    (boundary.comp₂ Primrec₂.right)
    (terminal.comp₂ Primrec₂.right)).of_eq fun node => by
      cases node with
      | boundary value =>
          rcases value with ⟨crossing, side⟩
          cases side <;> rfl
      | terminal value => rfl

theorem CarrierNode.orderCoordinate_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (CarrierNode.orderCoordinate :
      PeriodicGraph Vertex → CarrierNode → Int) := by
  change Primrec fun input : PeriodicGraph Vertex × CarrierNode =>
    input.2.orderCoordinate input.1
  have position : Primrec fun input :
      PeriodicGraph Vertex × CarrierNode =>
      input.2.position input.1 := CarrierNode.position_primrec
  have horizontal : PrimrecPred fun input :
      PeriodicGraph Vertex × CarrierNode =>
      input.2.isHorizontal = true :=
    Primrec.eq.comp
      (CarrierNode.isHorizontal_primrec.comp Primrec.snd)
      (Primrec.const true)
  exact (Primrec.ite horizontal
    (Primrec.fst.comp position)
    (Primrec.snd.comp position)).of_eq fun input => by
      simp [CarrierNode.orderCoordinate]

theorem retainedCompleteCarrierNodes_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (retainedCompleteCarrierNodes :
      PeriodicGraph Vertex → (Nat × Nat × Cell) → List CarrierNode) := by
  let Input := PeriodicGraph Vertex × (Nat × Nat × Cell)
  have nodes : Primrec fun input : Input =>
      retainedDrawingCarrierNodes input.1 :=
    retainedDrawingCarrierNodes_primrec.comp Primrec.fst
  have deduped : Primrec fun input : Input =>
      (retainedDrawingCarrierNodes input.1).dedup :=
    PeriodicThreeSATThree.dedup_primrec.comp nodes
  have sameKey : PrimrecRel fun (node : CarrierNode)
      (key : Nat × Nat × Cell) => node.carrierKey = key :=
    Primrec.eq.comp₂
      (CarrierNode.carrierKey_primrec.comp₂ Primrec₂.left)
      Primrec₂.right
  have selected : Primrec fun input : Input =>
      (retainedDrawingCarrierNodes input.1).dedup.filter fun node =>
        node.carrierKey = input.2 :=
    sameKey.listFilter.comp deduped Primrec.snd
  let lessEq : Input → CarrierNode → CarrierNode → Bool :=
    fun input first second => decide
      (first.orderCoordinate input.1 ≤ second.orderCoordinate input.1)
  have lessEqPrimrec : Primrec fun input :
      (Input × CarrierNode) × CarrierNode =>
      lessEq input.1.1 input.1.2 input.2 :=
    Computability.int_le_primrec.decide.comp
      (CarrierNode.orderCoordinate_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
      (CarrierNode.orderCoordinate_primrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have sorted := Computability.boolInsertionSort_primrec
    (fun input : Input =>
      (retainedDrawingCarrierNodes input.1).dedup.filter fun node =>
        node.carrierKey = input.2)
    lessEq selected lessEqPrimrec
  exact sorted.of_eq fun input =>
    Computability.boolInsertionSort_eq_insertionSort
      (lessEq input)
      (fun first second =>
        first.orderCoordinate input.1 ≤ second.orderCoordinate input.1)
      (fun _ _ => by simp [lessEq]) _

theorem CarrierNode.sameCrossoverSite_primrec :
    Primrec₂ CarrierNode.sameCrossoverSite := by
  change Primrec fun input : CarrierNode × CarrierNode =>
    input.1.sameCrossoverSite input.2
  let crossing? : CarrierNode → Option CrossingRecord := fun node =>
    Sum.casesOn (CarrierNode.equivData node)
      (fun boundary => some boundary.crossing) (fun _ => none)
  have crossingPrimrec : Primrec crossing? :=
    Primrec.sumCasesOn CarrierNode.equivData_primrec
      ((Primrec.option_some.comp
        CrossingBoundary.crossing_primrec).comp₂ Primrec₂.right)
      (Primrec.const none).to₂
  have first : Primrec fun input : CarrierNode × CarrierNode =>
      crossing? input.1 := crossingPrimrec.comp Primrec.fst
  have second : Primrec fun input : CarrierNode × CarrierNode =>
      crossing? input.2 := crossingPrimrec.comp Primrec.snd
  let optionEqual : Option CrossingRecord → Option CrossingRecord → Bool :=
    fun first second => decide (first = second)
  have optionEq : Primrec₂ optionEqual := Primrec.eq.decide
  have same : Primrec fun input : CarrierNode × CarrierNode =>
      optionEqual (crossing? input.1) (crossing? input.2) :=
    optionEq.comp first second
  have result : Primrec fun input : CarrierNode × CarrierNode =>
      (crossing? input.1).isSome &&
        optionEqual (crossing? input.1) (crossing? input.2) :=
    Primrec.and.comp (Primrec.option_isSome.comp first) same
  exact result.of_eq fun input => by
    rcases input with ⟨first, second⟩
    cases first <;> cases second <;>
      simp [CarrierNode.sameCrossoverSite, crossing?, optionEqual,
        CarrierNode.equivData]

theorem consecutivePairs_primrec
    {Value : Type*} [Primcodable Value] :
    Primrec (@consecutivePairs Value) := by
  have step : Primrec₂ fun (_list : List Value)
      (state : Value × List Value × List (Value × Value)) =>
      match state.2.1.head? with
      | none => []
      | some second => (state.1, second) :: state.2.2 := by
    change Primrec fun combined : List Value ×
        (Value × List Value × List (Value × Value)) =>
      match combined.2.2.1.head? with
      | none => []
      | some second =>
          (combined.2.1, second) :: combined.2.2.2
    have next : Primrec fun combined : List Value ×
        (Value × List Value × List (Value × Value)) =>
        combined.2.2.1.head? :=
      Primrec.list_head?.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have selected : Primrec fun input :
        (List Value × (Value × List Value × List (Value × Value))) ×
          Value =>
        (input.1.2.1, input.2) :: input.1.2.2.2 := by
      exact Primrec.list_cons.comp
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact (Primrec.option_casesOn next
      (Primrec.const []) selected.to₂).of_eq fun combined => by
        cases combined.2.2.1.head? <;> rfl
  have recursion := Primrec.list_rec
    (f := fun list : List Value => list)
    (g := fun _ => ([] : List (Value × Value)))
    (h := fun _ state =>
      match state.2.1.head? with
      | none => []
      | some second => (state.1, second) :: state.2.2)
    Primrec.id (Primrec.const []) step
  exact recursion.of_eq fun list => by
    induction list with
    | nil => rfl
    | cons first rest induction =>
        cases rest with
        | nil => rfl
        | cons second tail =>
            change (first, second) ::
                (List.recOn (second :: tail) [] fun head rest recursive =>
                  match rest.head? with
                  | none => []
                  | some next => (head, next) :: recursive) =
              (first, second) :: consecutivePairs (second :: tail)
            exact congrArg (List.cons (first, second)) induction

theorem carrierNodeEqualityPositions_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input :
        (PeriodicGraph Vertex × CarrierNode) × CarrierNode =>
      carrierNodeEqualityPositions input.1.1 input.1.2 input.2 := by
  let Input := (PeriodicGraph Vertex × CarrierNode) × CarrierNode
  have graph : Primrec fun input : Input => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  have firstNode : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have firstPosition : Primrec fun input : Input =>
      input.1.2.position input.1.1 :=
    CarrierNode.position_primrec.comp graph firstNode
  have secondPosition : Primrec fun input : Input =>
      input.2.position input.1.1 :=
    CarrierNode.position_primrec.comp graph Primrec.snd
  have horizontal : PrimrecPred fun input : Input =>
      input.1.2.isHorizontal = true :=
    Primrec.eq.comp
      (CarrierNode.isHorizontal_primrec.comp firstNode)
      (Primrec.const true)
  have xForward : PrimrecPred fun input : Input =>
      (input.1.2.position input.1.1).1 ≤
        (input.2.position input.1.1).1 :=
    Computability.int_le_primrec.comp
      (Primrec.fst.comp firstPosition)
      (Primrec.fst.comp secondPosition)
  have yForward : PrimrecPred fun input : Input =>
      (input.1.2.position input.1.1).2 ≤
        (input.2.position input.1.1).2 :=
    Computability.int_le_primrec.comp
      (Primrec.snd.comp firstPosition)
      (Primrec.snd.comp secondPosition)
  let xStep : Input → Int := fun input =>
    if (input.1.2.position input.1.1).1 ≤
        (input.2.position input.1.1).1 then 1 else -1
  let yStep : Input → Int := fun input =>
    if (input.1.2.position input.1.1).2 ≤
        (input.2.position input.1.1).2 then 1 else -1
  have xStepPrimrec : Primrec xStep :=
    Primrec.ite xForward (Primrec.const (1 : Int))
      (Primrec.const (-1 : Int))
  have yStepPrimrec : Primrec yStep :=
    Primrec.ite yForward (Primrec.const (1 : Int))
      (Primrec.const (-1 : Int))
  have scaled (coefficient : Int) (step : Input → Int)
      (stepPrimrec : Primrec step) : Primrec fun input : Input =>
      coefficient * step input :=
    Computability.int_multiply_primrec.comp
      (Primrec.const coefficient) stepPrimrec
  have horizontalOffset (coefficient : Int) :
      Primrec fun input : Input =>
        (coefficient * xStep input, (0 : Int)) :=
    Primrec.pair (scaled coefficient xStep xStepPrimrec)
      (Primrec.const (0 : Int))
  have verticalOffset (coefficient : Int) :
      Primrec fun input : Input =>
        ((0 : Int), coefficient * yStep input) :=
    Primrec.pair (Primrec.const (0 : Int))
      (scaled coefficient yStep yStepPrimrec)
  have forward : Primrec fun input : Input =>
      if input.1.2.isHorizontal then
        Cell.add (input.1.2.position input.1.1)
          (3 * xStep input, 0)
      else
        Cell.add (input.1.2.position input.1.1)
          (0, 3 * yStep input) :=
    Primrec.ite horizontal
      (Computability.cell_add_primrec.comp firstPosition
        (horizontalOffset 3))
      (Computability.cell_add_primrec.comp firstPosition
        (verticalOffset 3))
  have backward : Primrec fun input : Input =>
      if input.1.2.isHorizontal then
        Cell.add (input.1.2.position input.1.1)
          (6 * xStep input, 0)
      else
        Cell.add (input.1.2.position input.1.1)
          (0, 6 * yStep input) :=
    Primrec.ite horizontal
      (Computability.cell_add_primrec.comp firstPosition
        (horizontalOffset 6))
      (Computability.cell_add_primrec.comp firstPosition
        (verticalOffset 6))
  exact (EqualityPositions.mk_primrec.comp
    (Primrec.pair forward backward)).of_eq fun input => by
      by_cases isHorizontal : input.1.2.isHorizontal = true
      · simp [carrierNodeEqualityPositions, xStep, isHorizontal]
      · simp [carrierNodeEqualityPositions, yStep, isHorizontal]

theorem carrierNodePairLink_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (carrierNodePairLink :
      PeriodicGraph Vertex → CarrierNode × CarrierNode →
        PlanarThreeSAT.EqualityLink CarrierNode) := by
  change Primrec fun input :
      PeriodicGraph Vertex × (CarrierNode × CarrierNode) =>
    carrierNodePairLink input.1 input.2
  have positions : Primrec fun input :
      PeriodicGraph Vertex × (CarrierNode × CarrierNode) =>
      carrierNodeEqualityPositions input.1 input.2.1 input.2.2 :=
    carrierNodeEqualityPositions_primrec.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact (EqualityLink.mk_primrec.comp
    (Primrec.pair Primrec.snd positions)).of_eq fun _ => rfl

theorem retainedCompleteCarrierLinks_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (retainedCompleteCarrierLinks :
      PeriodicGraph Vertex → (Nat × Nat × Cell) →
        List (PlanarThreeSAT.EqualityLink CarrierNode)) := by
  let Input := PeriodicGraph Vertex × (Nat × Nat × Cell)
  have pairs : Primrec fun input : Input =>
      consecutivePairs
        (retainedCompleteCarrierNodes input.1 input.2) :=
    consecutivePairs_primrec.comp retainedCompleteCarrierNodes_primrec
  have distinctSite : PrimrecPred fun pair : CarrierNode × CarrierNode =>
      pair.1.sameCrossoverSite pair.2 = false :=
    Primrec.eq.comp CarrierNode.sameCrossoverSite_primrec
      (Primrec.const false)
  have selected : Primrec fun input : Input =>
      (consecutivePairs
        (retainedCompleteCarrierNodes input.1 input.2)).filter fun pair =>
          !pair.1.sameCrossoverSite pair.2 :=
    ((Primrec.listFilter distinctSite).comp pairs).of_eq fun _ => by
      apply List.filter_congr
      intro pair _
      cases pair.1.sameCrossoverSite pair.2 <;> rfl
  exact Primrec.list_map selected
    (carrierNodePairLink_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

theorem retainedDrawingCompleteCarrierKeys_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingCompleteCarrierKeys :
      PeriodicGraph Vertex → List (Nat × Nat × Cell)) := by
  have keys : Primrec fun graph : PeriodicGraph Vertex =>
      (retainedDrawingCarrierNodes graph).map CarrierNode.carrierKey :=
    Primrec.list_map retainedDrawingCarrierNodes_primrec
      (CarrierNode.carrierKey_primrec.comp₂ Primrec₂.right)
  exact PeriodicThreeSATThree.dedup_primrec.comp keys

theorem retainedDrawingCompleteCarrierLinksRaw_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingCompleteCarrierLinksRaw :
      PeriodicGraph Vertex →
        List (PlanarThreeSAT.EqualityLink CarrierNode)) :=
  Primrec.list_flatMap retainedDrawingCompleteCarrierKeys_primrec
    retainedCompleteCarrierLinks_primrec

theorem crossingPeriodShift_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (crossingPeriodShift :
      PeriodicGraph Vertex → CrossingRecord → Cell) := by
  change Primrec fun input : PeriodicGraph Vertex × CrossingRecord =>
    crossingPeriodShift input.1 input.2
  have point : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord => input.2.point :=
    CrossingRecord.point_primrec.comp Primrec.snd
  have size : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord => drawingGridSize input.1 :=
    drawingGridSize_primrec.comp Primrec.fst
  exact Primrec.pair
    (Computability.int_edivNat_primrec.comp
      (Primrec.fst.comp point) size)
    (Computability.int_edivNat_primrec.comp
      (Primrec.snd.comp point) size)

theorem carrierLinkRepresentativeShift_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (carrierLinkRepresentativeShift :
      PeriodicGraph Vertex →
        PlanarThreeSAT.EqualityLink CarrierNode → Cell) := by
  let Input := PeriodicGraph Vertex ×
    PlanarThreeSAT.EqualityLink CarrierNode
  have firstData : Primrec fun input : Input =>
      CarrierNode.equivData input.2.first :=
    CarrierNode.equivData_primrec.comp
      (EqualityLink.first_primrec.comp Primrec.snd)
  have firstBoundary : Primrec₂ fun (input : Input)
      (boundary : CrossingBoundary) =>
      crossingPeriodShift input.1 boundary.crossing :=
    crossingPeriodShift_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (CrossingBoundary.crossing_primrec.comp₂ Primrec₂.right)
  have firstTerminal : Primrec₂ fun (input : Input)
      (terminal : SegmentTerminal) =>
      match input.2.second with
      | .boundary boundary =>
          crossingPeriodShift input.1 boundary.crossing
      | .terminal _ => terminal.translate := by
    have secondData : Primrec fun input : Input × SegmentTerminal =>
        CarrierNode.equivData input.1.2.second :=
      CarrierNode.equivData_primrec.comp
        (EqualityLink.second_primrec.comp
          (Primrec.snd.comp Primrec.fst))
    have secondBoundary : Primrec₂ fun
        (input : Input × SegmentTerminal)
        (boundary : CrossingBoundary) =>
        crossingPeriodShift input.1.1 boundary.crossing :=
      crossingPeriodShift_primrec.comp₂
        ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left)
        (CrossingBoundary.crossing_primrec.comp₂ Primrec₂.right)
    have secondTerminal : Primrec₂ fun
        (input : Input × SegmentTerminal)
        (_second : SegmentTerminal) => input.2.translate :=
      SegmentTerminal.translate_primrec.comp₂
        (Primrec.snd.comp₂ Primrec₂.left)
    exact (Primrec.sumCasesOn secondData
      secondBoundary secondTerminal).of_eq fun input => by
        rcases input with ⟨⟨graph, link⟩, terminal⟩
        cases secondEq : link.second <;>
          simp [CarrierNode.equivData, secondEq]
  exact (Primrec.sumCasesOn firstData
    firstBoundary firstTerminal).of_eq fun input => by
      rcases input with ⟨graph, link⟩
      cases firstEq : link.first with
      | boundary boundary =>
          simp [carrierLinkRepresentativeShift, CarrierNode.equivData,
            firstEq]
      | terminal terminal =>
          cases secondEq : link.second <;>
            simp [carrierLinkRepresentativeShift, CarrierNode.equivData,
              firstEq, secondEq]

theorem carrierLinkIsRepresentative_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    PrimrecRel fun (link : PlanarThreeSAT.EqualityLink CarrierNode)
        (graph : PeriodicGraph Vertex) =>
      CarrierLinkIsRepresentative graph link := by
  change PrimrecPred fun input :
      PlanarThreeSAT.EqualityLink CarrierNode × PeriodicGraph Vertex =>
    carrierLinkRepresentativeShift input.2 input.1 = (0, 0)
  exact Primrec.eq.comp
    (carrierLinkRepresentativeShift_primrec.comp
      Primrec.snd Primrec.fst)
    (Primrec.const (0, 0))

theorem retainedDrawingCompleteCarrierLinks_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingCompleteCarrierLinks :
      PeriodicGraph Vertex →
        List (PlanarThreeSAT.EqualityLink CarrierNode)) :=
  carrierLinkIsRepresentative_primrec.listFilter.comp
    retainedDrawingCompleteCarrierLinksRaw_primrec Primrec.id

theorem retainedDrawingCompleteCarrierLinks_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (retainedDrawingCompleteCarrierLinks :
      PeriodicGraph Vertex →
        List (PlanarThreeSAT.EqualityLink CarrierNode)) :=
  retainedDrawingCompleteCarrierLinks_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes

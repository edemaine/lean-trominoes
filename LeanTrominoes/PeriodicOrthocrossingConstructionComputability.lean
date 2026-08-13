/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphComputability
import LeanTrominoes.PeriodicOrthocrossingConstruction

/-!
# Computability of the orthocrossing track construction

The explicit track drawing used to planarize a finite periodic graph is
primitive recursive.  This includes finite edge-end ports, their ranks and
coordinates, and the complete source-to-target polyline of every protoedge.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1600000

namespace PortEnd

def equivBool : PortEnd ≃ Bool where
  toFun
    | .source => false
    | .target => true
  invFun
    | false => .source
    | true => .target
  left_inv endKind := by cases endKind <;> rfl
  right_inv value := by cases value <;> rfl

noncomputable instance : Primcodable PortEnd :=
  Primcodable.ofEquiv Bool equivBool

theorem equivBool_primrec : Primrec equivBool :=
  Primrec.of_equiv

theorem equivBool_symm_primrec : Primrec equivBool.symm :=
  Primrec.of_equiv_symm

end PortEnd

namespace GraphPort

def equivData {Vertex : Type*} :
    GraphPort Vertex ≃ Vertex × Nat × PortEnd where
  toFun port := (port.vertex, port.edgeIndex, port.endKind)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv port := by cases port; rfl
  right_inv data := by rcases data with ⟨vertex, edgeIndex, endKind⟩; rfl

noncomputable instance {Vertex : Type*} [Primcodable Vertex] :
    Primcodable (GraphPort Vertex) :=
  Primcodable.ofEquiv (Vertex × Nat × PortEnd) equivData

theorem equivData_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@equivData Vertex) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@equivData Vertex).symm :=
  Primrec.of_equiv_symm

theorem vertex_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@GraphPort.vertex Vertex) :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem edgeIndex_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@GraphPort.edgeIndex Vertex) :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem endKind_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (@GraphPort.endKind Vertex) :=
  ((Primrec.snd.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec fun data : Vertex × Nat × PortEnd =>
      GraphPort.mk data.1 data.2.1 data.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end GraphPort

theorem edgePorts_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (edgePorts :
      PeriodicEdge Vertex × Nat → List (GraphPort Vertex)) := by
  have source : Primrec fun input : PeriodicEdge Vertex × Nat =>
      GraphPort.mk input.1.source input.2 .source :=
    GraphPort.mk_primrec.comp
      (Primrec.pair
        (PeriodicEdge.source_primrec.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.const .source)))
  have target : Primrec fun input : PeriodicEdge Vertex × Nat =>
      GraphPort.mk input.1.target input.2 .target :=
    GraphPort.mk_primrec.comp
      (Primrec.pair
        (PeriodicEdge.target_primrec.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.const .target)))
  exact (Primrec.list_cons.comp source
    (Primrec.list_cons.comp target (Primrec.const []))).of_eq
      fun _ => rfl

theorem allPorts_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (allPorts :
      PeriodicGraph Vertex → List (GraphPort Vertex)) := by
  have tagged : Primrec fun graph : PeriodicGraph Vertex =>
      graph.edges.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicGraph.edges_primrec
  exact Primrec.list_flatMap tagged
    (edgePorts_primrec.comp Primrec.snd).to₂

theorem portsAt_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (portsAt : PeriodicGraph Vertex → Vertex →
      List (GraphPort Vertex)) := by
  have same : PrimrecRel fun (port : GraphPort Vertex)
      (vertex : Vertex) => port.vertex = vertex :=
    Primrec.eq.comp₂
      (GraphPort.vertex_primrec.comp₂ Primrec₂.left)
      Primrec₂.right
  exact same.listFilter.comp
    (allPorts_primrec.comp Primrec.fst) Primrec.snd

theorem drawingGridSize_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (drawingGridSize : PeriodicGraph Vertex → Nat) := by
  have size : Primrec fun graph : PeriodicGraph Vertex =>
      graph.vertices.length + graph.edges.length + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.list_length.comp PeriodicGraph.vertices_primrec)
        (Primrec.list_length.comp PeriodicGraph.edges_primrec))
      (Primrec.const 1)
  exact (Primrec.nat_mul.comp (Primrec.const 16) size).of_eq
    fun _ => rfl

theorem vertexX_primrec : Primrec vertexX := by
  have scaled : Primrec fun index : Nat =>
      (8 : Int) * Int.ofNat index :=
    Computability.int_multiply_primrec.comp
      (Primrec.const (8 : Int)) Computability.int_ofNat_primrec
  exact (Computability.int_add_primrec.comp scaled
    (Primrec.const (4 : Int))).of_eq fun _ => rfl

theorem vertexPosition_primrec : Primrec vertexPosition := by
  exact (Primrec.pair vertexX_primrec
    (Primrec.const (2 : Int))).of_eq fun _ => rfl

theorem portRank_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (portRank : PeriodicGraph Vertex → GraphPort Vertex → Nat) := by
  change Primrec fun input : PeriodicGraph Vertex × GraphPort Vertex =>
    portRank input.1 input.2
  have ports : Primrec fun input :
      PeriodicGraph Vertex × GraphPort Vertex =>
      portsAt input.1 input.2.vertex :=
    portsAt_primrec.comp Primrec.fst
      (GraphPort.vertex_primrec.comp Primrec.snd)
  exact (Primrec.list_idxOf.comp Primrec.snd ports).of_eq
    fun _ => rfl

theorem portX_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (portX : PeriodicGraph Vertex → GraphPort Vertex → Int) := by
  change Primrec fun input : PeriodicGraph Vertex × GraphPort Vertex =>
    portX input.1 input.2
  have vertexIndex : Primrec fun input :
      PeriodicGraph Vertex × GraphPort Vertex =>
      input.1.vertices.idxOf input.2.vertex :=
    Primrec.list_idxOf.comp
      (GraphPort.vertex_primrec.comp Primrec.snd)
      (PeriodicGraph.vertices_primrec.comp Primrec.fst)
  have rank : Primrec fun input :
      PeriodicGraph Vertex × GraphPort Vertex =>
      portRank input.1 input.2 :=
    portRank_primrec
  have twiceRank : Primrec fun input :
      PeriodicGraph Vertex × GraphPort Vertex =>
      (2 : Int) * Int.ofNat (portRank input.1 input.2) :=
    Computability.int_multiply_primrec.comp
      (Primrec.const (2 : Int))
      (Computability.int_ofNat_primrec.comp rank)
  exact (Computability.int_subtract_primrec.comp
    (Computability.int_add_primrec.comp
      (vertexX_primrec.comp vertexIndex) twiceRank)
    (Primrec.const (2 : Int))).of_eq fun _ => rfl

theorem portPosition_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (portPosition :
      PeriodicGraph Vertex → GraphPort Vertex → Cell) := by
  change Primrec fun input : PeriodicGraph Vertex × GraphPort Vertex =>
    portPosition input.1 input.2
  exact (Primrec.pair portX_primrec
    (Primrec.const (3 : Int))).of_eq fun _ => rfl

theorem edgeTrack_primrec : Primrec edgeTrack := by
  have scaled : Primrec fun edgeIndex : Nat =>
      (4 : Int) * Int.ofNat edgeIndex :=
    Computability.int_multiply_primrec.comp
      (Primrec.const (4 : Int)) Computability.int_ofNat_primrec
  exact (Computability.int_add_primrec.comp
    (Primrec.const (6 : Int)) scaled).of_eq fun _ => rfl

theorem edgeGateX_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec₂ (edgeGateX : PeriodicGraph Vertex → Nat → Int) := by
  change Primrec fun input : PeriodicGraph Vertex × Nat =>
    edgeGateX input.1 input.2
  have vertexTerm : Primrec fun input : PeriodicGraph Vertex × Nat =>
      (8 : Int) * Int.ofNat input.1.vertices.length :=
    Computability.int_multiply_primrec.comp
      (Primrec.const (8 : Int))
      (Computability.int_ofNat_primrec.comp
        (Primrec.list_length.comp
          (PeriodicGraph.vertices_primrec.comp Primrec.fst)))
  have edgeTerm : Primrec fun input : PeriodicGraph Vertex × Nat =>
      (2 : Int) * Int.ofNat input.2 :=
    Computability.int_multiply_primrec.comp
      (Primrec.const (2 : Int))
      (Computability.int_ofNat_primrec.comp Primrec.snd)
  exact (Computability.int_add_primrec.comp
    (Computability.int_add_primrec.comp vertexTerm
      (Primrec.const (4 : Int))) edgeTerm).of_eq fun _ => rfl

theorem joinPolylines_primrec : Primrec₂ joinPolylines := by
  unfold joinPolylines
  exact Primrec.list_append.comp₂ Primrec₂.left
    (Primrec.list_tail.comp₂ Primrec₂.right)

theorem fanout_primrec :
    Primrec fun input : Int × Int => fanout input.1 input.2 := by
  have same : PrimrecPred fun input : Int × Int => input.1 = input.2 :=
    Primrec.eq.comp Primrec.fst Primrec.snd
  have first : Primrec fun input : Int × Int =>
      ((input.1, 2) : Cell) :=
    Primrec.pair Primrec.fst (Primrec.const (2 : Int))
  have middle : Primrec fun input : Int × Int =>
      ((input.2, 2) : Cell) :=
    Primrec.pair Primrec.snd (Primrec.const (2 : Int))
  have last : Primrec fun input : Int × Int =>
      ((input.2, 3) : Cell) :=
    Primrec.pair Primrec.snd (Primrec.const (3 : Int))
  have short : Primrec fun input : Int × Int =>
      [((input.1, 2) : Cell), (input.2, 3)] :=
    Primrec.list_cons.comp first
      (Primrec.list_cons.comp last (Primrec.const []))
  have long : Primrec fun input : Int × Int =>
      [((input.1, 2) : Cell), (input.2, 2), (input.2, 3)] :=
    Primrec.list_cons.comp first
      (Primrec.list_cons.comp middle
        (Primrec.list_cons.comp last (Primrec.const [])))
  exact (Primrec.ite same short long).of_eq fun input => by
    simp [fanout]

theorem translatePolyline_primrec :
    Primrec₂ translatePolyline := by
  change Primrec fun input : Cell × List Cell =>
    translatePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

theorem sourcePort_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec₂ (sourcePort :
      PeriodicEdge Vertex → Nat → GraphPort Vertex) := by
  change Primrec fun input : PeriodicEdge Vertex × Nat =>
    sourcePort input.1 input.2
  exact (GraphPort.mk_primrec.comp
    (Primrec.pair
      (PeriodicEdge.source_primrec.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.const .source)))).of_eq
        fun _ => rfl

theorem targetPort_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec₂ (targetPort :
      PeriodicEdge Vertex → Nat → GraphPort Vertex) := by
  change Primrec fun input : PeriodicEdge Vertex × Nat =>
    targetPort input.1 input.2
  exact (GraphPort.mk_primrec.comp
    (Primrec.pair
      (PeriodicEdge.target_primrec.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.const .target)))).of_eq
        fun _ => rfl

theorem edgeCore_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input :
        (PeriodicGraph Vertex × PeriodicEdge Vertex) × Nat =>
      edgeCore input.1.1 input.1.2 input.2 := by
  let Input := (PeriodicGraph Vertex × PeriodicEdge Vertex) × Nat
  let graph : Primrec fun input : Input => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  let edge : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  let edgeIndex : Primrec fun input : Input => input.2 := Primrec.snd
  let offset : Primrec fun input : Input => input.1.2.offset :=
    PeriodicEdge.offset_primrec.comp edge
  let size : Primrec fun input : Input =>
      Int.ofNat (drawingGridSize input.1.1) :=
    Computability.int_ofNat_primrec.comp
      (drawingGridSize_primrec.comp graph)
  let source : Primrec fun input : Input =>
      sourcePort input.1.2 input.2 :=
    sourcePort_primrec.comp edge edgeIndex
  let target : Primrec fun input : Input =>
      targetPort input.1.2 input.2 :=
    targetPort_primrec.comp edge edgeIndex
  let sourceX : Primrec fun input : Input =>
      portX input.1.1 (sourcePort input.1.2 input.2) :=
    portX_primrec.comp graph source
  let targetX : Primrec fun input : Input =>
      portX input.1.1 (targetPort input.1.2 input.2) :=
    portX_primrec.comp graph target
  let sourcePoint : Primrec fun input : Input =>
      ((portX input.1.1 (sourcePort input.1.2 input.2), 3) : Cell) :=
    Primrec.pair sourceX (Primrec.const (3 : Int))
  let targetBase : Primrec fun input : Input =>
      ((portX input.1.1 (targetPort input.1.2 input.2), 3) : Cell) :=
    Primrec.pair targetX (Primrec.const (3 : Int))
  let targetTranslate : Primrec fun input : Input =>
      Cell.scale (Int.ofNat (drawingGridSize input.1.1))
        input.1.2.offset :=
    Computability.cell_scale_primrec.comp size offset
  let targetPoint : Primrec fun input : Input =>
      Cell.add
        (portX input.1.1 (targetPort input.1.2 input.2), 3)
        (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
          input.1.2.offset) :=
    Computability.cell_add_primrec.comp targetBase targetTranslate
  let low : Primrec fun input : Input => edgeTrack input.2 :=
    edgeTrack_primrec.comp edgeIndex
  let high : Primrec fun input : Input => edgeTrack input.2 + 1 :=
    Computability.int_add_primrec.comp low (Primrec.const (1 : Int))
  let gate : Primrec fun input : Input =>
      edgeGateX input.1.1 input.2 :=
    edgeGateX_primrec.comp graph edgeIndex
  have sourceLow : Primrec fun input : Input =>
      ((portX input.1.1 (sourcePort input.1.2 input.2),
        edgeTrack input.2) : Cell) :=
    Primrec.pair sourceX low
  have sourceHigh : Primrec fun input : Input =>
      ((portX input.1.1 (sourcePort input.1.2 input.2),
        edgeTrack input.2 + 1) : Cell) :=
    Primrec.pair sourceX high
  have targetLow : Primrec fun input : Input =>
      ((portX input.1.1 (targetPort input.1.2 input.2),
        edgeTrack input.2) : Cell) :=
    Primrec.pair targetX low
  have sizePlusTargetX : Primrec fun input : Input =>
      Int.ofNat (drawingGridSize input.1.1) +
        portX input.1.1 (targetPort input.1.2 input.2) :=
    Computability.int_add_primrec.comp size targetX
  have targetXMinusSize : Primrec fun input : Input =>
      portX input.1.1 (targetPort input.1.2 input.2) -
        Int.ofNat (drawingGridSize input.1.1) :=
    Computability.int_subtract_primrec.comp targetX size
  have sizePlusLow : Primrec fun input : Input =>
      Int.ofNat (drawingGridSize input.1.1) + edgeTrack input.2 :=
    Computability.int_add_primrec.comp size low
  have highMinusSize : Primrec fun input : Input =>
      edgeTrack input.2 + 1 - Int.ofNat (drawingGridSize input.1.1) :=
    Computability.int_subtract_primrec.comp high size
  have finish : Primrec fun input : Input =>
      [Cell.add
        (portX input.1.1 (targetPort input.1.2 input.2), 3)
        (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
          input.1.2.offset)] :=
    Primrec.list_cons.comp targetPoint (Primrec.const [])
  have zeroRoute : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        (portX input.1.1 (targetPort input.1.2 input.2), edgeTrack input.2),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp targetLow finish))
  have rightShortPoint : Primrec fun input : Input =>
      ((Int.ofNat (drawingGridSize input.1.1) +
          portX input.1.1 (targetPort input.1.2 input.2),
        edgeTrack input.2) : Cell) :=
    Primrec.pair sizePlusTargetX low
  have rightShort : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        (Int.ofNat (drawingGridSize input.1.1) +
          portX input.1.1 (targetPort input.1.2 input.2), edgeTrack input.2),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp rightShortPoint finish))
  have sizeLow : Primrec fun input : Input =>
      ((Int.ofNat (drawingGridSize input.1.1), edgeTrack input.2) : Cell) :=
    Primrec.pair size low
  have sizeHigh : Primrec fun input : Input =>
      ((Int.ofNat (drawingGridSize input.1.1), edgeTrack input.2 + 1) : Cell) :=
    Primrec.pair size high
  have rightHigh : Primrec fun input : Input =>
      ((Int.ofNat (drawingGridSize input.1.1) +
          portX input.1.1 (targetPort input.1.2 input.2),
        edgeTrack input.2 + 1) : Cell) :=
    Primrec.pair sizePlusTargetX high
  have rightLong : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        (Int.ofNat (drawingGridSize input.1.1), edgeTrack input.2),
        (Int.ofNat (drawingGridSize input.1.1), edgeTrack input.2 + 1),
        (Int.ofNat (drawingGridSize input.1.1) +
          portX input.1.1 (targetPort input.1.2 input.2),
          edgeTrack input.2 + 1),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp sizeLow
          (Primrec.list_cons.comp sizeHigh
            (Primrec.list_cons.comp rightHigh finish))))
  have leftShortPoint : Primrec fun input : Input =>
      ((portX input.1.1 (targetPort input.1.2 input.2) -
          Int.ofNat (drawingGridSize input.1.1),
        edgeTrack input.2) : Cell) :=
    Primrec.pair targetXMinusSize low
  have leftShort : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        (portX input.1.1 (targetPort input.1.2 input.2) -
          Int.ofNat (drawingGridSize input.1.1), edgeTrack input.2),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp leftShortPoint finish))
  have zeroLow : Primrec fun input : Input =>
      (((0 : Int), edgeTrack input.2) : Cell) :=
    Primrec.pair (Primrec.const (0 : Int)) low
  have zeroHigh : Primrec fun input : Input =>
      (((0 : Int), edgeTrack input.2 + 1) : Cell) :=
    Primrec.pair (Primrec.const (0 : Int)) high
  have leftHigh : Primrec fun input : Input =>
      ((portX input.1.1 (targetPort input.1.2 input.2) -
          Int.ofNat (drawingGridSize input.1.1),
        edgeTrack input.2 + 1) : Cell) :=
    Primrec.pair targetXMinusSize high
  have leftLong : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        ((0 : Int), edgeTrack input.2),
        ((0 : Int), edgeTrack input.2 + 1),
        (portX input.1.1 (targetPort input.1.2 input.2) -
          Int.ofNat (drawingGridSize input.1.1), edgeTrack input.2 + 1),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp zeroLow
          (Primrec.list_cons.comp zeroHigh
            (Primrec.list_cons.comp leftHigh finish))))
  have gateHigh : Primrec fun input : Input =>
      ((edgeGateX input.1.1 input.2, edgeTrack input.2 + 1) : Cell) :=
    Primrec.pair gate high
  have gateSizePlusLow : Primrec fun input : Input =>
      ((edgeGateX input.1.1 input.2,
        Int.ofNat (drawingGridSize input.1.1) + edgeTrack input.2) : Cell) :=
    Primrec.pair gate sizePlusLow
  have targetSizePlusLow : Primrec fun input : Input =>
      ((portX input.1.1 (targetPort input.1.2 input.2),
        Int.ofNat (drawingGridSize input.1.1) + edgeTrack input.2) : Cell) :=
    Primrec.pair targetX sizePlusLow
  have upRoute : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2 + 1),
        (edgeGateX input.1.1 input.2, edgeTrack input.2 + 1),
        (edgeGateX input.1.1 input.2,
          Int.ofNat (drawingGridSize input.1.1) + edgeTrack input.2),
        (portX input.1.1 (targetPort input.1.2 input.2),
          Int.ofNat (drawingGridSize input.1.1) + edgeTrack input.2),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceHigh
        (Primrec.list_cons.comp gateHigh
          (Primrec.list_cons.comp gateSizePlusLow
            (Primrec.list_cons.comp targetSizePlusLow finish))))
  have gateLow : Primrec fun input : Input =>
      ((edgeGateX input.1.1 input.2, edgeTrack input.2) : Cell) :=
    Primrec.pair gate low
  have gateHighMinusSize : Primrec fun input : Input =>
      ((edgeGateX input.1.1 input.2,
        edgeTrack input.2 + 1 -
          Int.ofNat (drawingGridSize input.1.1)) : Cell) :=
    Primrec.pair gate highMinusSize
  have targetHighMinusSize : Primrec fun input : Input =>
      ((portX input.1.1 (targetPort input.1.2 input.2),
        edgeTrack input.2 + 1 -
          Int.ofNat (drawingGridSize input.1.1)) : Cell) :=
    Primrec.pair targetX highMinusSize
  have downRoute : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        (edgeGateX input.1.1 input.2, edgeTrack input.2),
        (edgeGateX input.1.1 input.2,
          edgeTrack input.2 + 1 - Int.ofNat (drawingGridSize input.1.1)),
        (portX input.1.1 (targetPort input.1.2 input.2),
          edgeTrack input.2 + 1 - Int.ofNat (drawingGridSize input.1.1)),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp gateLow
          (Primrec.list_cons.comp gateHighMinusSize
            (Primrec.list_cons.comp targetHighMinusSize finish))))
  have fallbackMiddle : Primrec fun input : Input =>
      (((Cell.add
        (portX input.1.1 (targetPort input.1.2 input.2), 3)
        (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
          input.1.2.offset)).1,
        edgeTrack input.2) : Cell) :=
    Primrec.pair (Primrec.fst.comp targetPoint) low
  have fallbackRoute : Primrec fun input : Input =>
      [ (portX input.1.1 (sourcePort input.1.2 input.2), 3),
        (portX input.1.1 (sourcePort input.1.2 input.2), edgeTrack input.2),
        ((Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset)).1, edgeTrack input.2),
        Cell.add
          (portX input.1.1 (targetPort input.1.2 input.2), 3)
          (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
            input.1.2.offset) ] :=
    Primrec.list_cons.comp sourcePoint
      (Primrec.list_cons.comp sourceLow
        (Primrec.list_cons.comp fallbackMiddle finish))
  let isOffset (value : Cell) : PrimrecPred fun input : Input =>
      input.1.2.offset = value :=
    Primrec.eq.comp offset (Primrec.const value)
  have targetBeforeSource : PrimrecPred fun input : Input =>
      portX input.1.1 (targetPort input.1.2 input.2) <
        portX input.1.1 (sourcePort input.1.2 input.2) :=
    Computability.int_lt_primrec.comp targetX sourceX
  have sourceBeforeTarget : PrimrecPred fun input : Input =>
      portX input.1.1 (sourcePort input.1.2 input.2) <
        portX input.1.1 (targetPort input.1.2 input.2) :=
    Computability.int_lt_primrec.comp sourceX targetX
  have implementation :=
    Primrec.ite (isOffset (0, 0)) zeroRoute
      (Primrec.ite (isOffset (1, 0))
        (Primrec.ite targetBeforeSource rightShort rightLong)
        (Primrec.ite (isOffset (-1, 0))
          (Primrec.ite sourceBeforeTarget leftShort leftLong)
          (Primrec.ite (isOffset (0, 1)) upRoute
            (Primrec.ite (isOffset (0, -1)) downRoute fallbackRoute))))
  exact implementation.of_eq fun input => by
    by_cases zero : input.1.2.offset = (0, 0)
    · simp [zero, edgeCore]
    by_cases right : input.1.2.offset = (1, 0)
    · simp [right, edgeCore]
    by_cases left : input.1.2.offset = (-1, 0)
    · simp [left, edgeCore]
    by_cases up : input.1.2.offset = (0, 1)
    · simp [up, edgeCore]
    by_cases down : input.1.2.offset = (0, -1)
    · simp [down, edgeCore]
    · generalize offsetEq : input.1.2.offset = offsetValue at zero right left up down ⊢
      rcases offsetValue with ⟨horizontal, vertical⟩
      have notZero : ¬ (horizontal = 0 ∧ vertical = 0) := by
        rintro ⟨rfl, rfl⟩
        exact zero rfl
      have notRight : ¬ (horizontal = 1 ∧ vertical = 0) := by
        rintro ⟨rfl, rfl⟩
        exact right rfl
      have notLeft : ¬ (horizontal = -1 ∧ vertical = 0) := by
        rintro ⟨rfl, rfl⟩
        exact left rfl
      have notUp : ¬ (horizontal = 0 ∧ vertical = 1) := by
        rintro ⟨rfl, rfl⟩
        exact up rfl
      have notDown : ¬ (horizontal = 0 ∧ vertical = -1) := by
        rintro ⟨rfl, rfl⟩
        exact down rfl
      simp [offsetEq, notZero, notRight, notLeft, notUp, notDown, edgeCore]

theorem constructedEdgeRoute_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input :
        (PeriodicGraph Vertex × PeriodicEdge Vertex) × Nat =>
      constructedEdgeRoute input.1.1 input.1.2 input.2 := by
  let Input := (PeriodicGraph Vertex × PeriodicEdge Vertex) × Nat
  let graph : Primrec fun input : Input => input.1.1 :=
    Primrec.fst.comp Primrec.fst
  let edge : Primrec fun input : Input => input.1.2 :=
    Primrec.snd.comp Primrec.fst
  let edgeIndex : Primrec fun input : Input => input.2 := Primrec.snd
  have sourceVertexIndex : Primrec fun input : Input =>
      input.1.1.vertices.idxOf input.1.2.source :=
    Primrec.list_idxOf.comp
      (PeriodicEdge.source_primrec.comp edge)
      (PeriodicGraph.vertices_primrec.comp graph)
  have targetVertexIndex : Primrec fun input : Input =>
      input.1.1.vertices.idxOf input.1.2.target :=
    Primrec.list_idxOf.comp
      (PeriodicEdge.target_primrec.comp edge)
      (PeriodicGraph.vertices_primrec.comp graph)
  have sourceCenter : Primrec fun input : Input =>
      vertexX (input.1.1.vertices.idxOf input.1.2.source) :=
    vertexX_primrec.comp sourceVertexIndex
  have targetCenter : Primrec fun input : Input =>
      vertexX (input.1.1.vertices.idxOf input.1.2.target) :=
    vertexX_primrec.comp targetVertexIndex
  have sourcePortValue : Primrec fun input : Input =>
      sourcePort input.1.2 input.2 :=
    sourcePort_primrec.comp edge edgeIndex
  have targetPortValue : Primrec fun input : Input =>
      targetPort input.1.2 input.2 :=
    targetPort_primrec.comp edge edgeIndex
  have sourceColumn : Primrec fun input : Input =>
      portX input.1.1 (sourcePort input.1.2 input.2) :=
    portX_primrec.comp graph sourcePortValue
  have targetColumn : Primrec fun input : Input =>
      portX input.1.1 (targetPort input.1.2 input.2) :=
    portX_primrec.comp graph targetPortValue
  have targetTranslate : Primrec fun input : Input =>
      Cell.scale (Int.ofNat (drawingGridSize input.1.1))
        input.1.2.offset :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (drawingGridSize_primrec.comp graph))
      (PeriodicEdge.offset_primrec.comp edge)
  have sourceFanout : Primrec fun input : Input =>
      fanout
        (vertexX (input.1.1.vertices.idxOf input.1.2.source))
        (portX input.1.1 (sourcePort input.1.2 input.2)) :=
    fanout_primrec.comp (Primrec.pair sourceCenter sourceColumn)
  have targetFanout : Primrec fun input : Input =>
      translatePolyline
        (Cell.scale (Int.ofNat (drawingGridSize input.1.1))
          input.1.2.offset)
        (fanout
          (vertexX (input.1.1.vertices.idxOf input.1.2.target))
          (portX input.1.1 (targetPort input.1.2 input.2))).reverse :=
    translatePolyline_primrec.comp targetTranslate
      (Primrec.list_reverse.comp
        (fanout_primrec.comp (Primrec.pair targetCenter targetColumn)))
  have core : Primrec fun input : Input =>
      edgeCore input.1.1 input.1.2 input.2 :=
    edgeCore_primrec
  have firstJoin : Primrec fun input : Input =>
      joinPolylines
        (fanout
          (vertexX (input.1.1.vertices.idxOf input.1.2.source))
          (portX input.1.1 (sourcePort input.1.2 input.2)))
        (edgeCore input.1.1 input.1.2 input.2) :=
    joinPolylines_primrec.comp sourceFanout core
  exact (joinPolylines_primrec.comp firstJoin targetFanout).of_eq
    fun _ => rfl

theorem constructedVertexPositions_primrec
    {Vertex : Type*} [Primcodable Vertex] :
    Primrec (constructedVertexPositions :
      PeriodicGraph Vertex → List Cell) := by
  have tagged : Primrec fun graph : PeriodicGraph Vertex =>
      graph.vertices.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicGraph.vertices_primrec
  exact (Primrec.list_map tagged
    (vertexPosition_primrec.comp
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

theorem constructedEdgeRoutes_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (constructedEdgeRoutes :
      PeriodicGraph Vertex → List (List Cell)) := by
  have tagged : Primrec fun graph : PeriodicGraph Vertex =>
      graph.edges.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicGraph.edges_primrec
  have route : Primrec₂ fun (graph : PeriodicGraph Vertex)
      (item : PeriodicEdge Vertex × Nat) =>
      constructedEdgeRoute graph item.1 item.2 := by
    change Primrec fun input :
        PeriodicGraph Vertex × (PeriodicEdge Vertex × Nat) =>
      constructedEdgeRoute input.1 input.2.1 input.2.2
    let graph : Primrec fun input :
        PeriodicGraph Vertex × (PeriodicEdge Vertex × Nat) =>
        input.1 := Primrec.fst
    let edge : Primrec fun input :
        PeriodicGraph Vertex × (PeriodicEdge Vertex × Nat) =>
        input.2.1 := Primrec.fst.comp Primrec.snd
    let edgeIndex : Primrec fun input :
        PeriodicGraph Vertex × (PeriodicEdge Vertex × Nat) =>
        input.2.2 := Primrec.snd.comp Primrec.snd
    exact constructedEdgeRoute_primrec.comp
      (Primrec.pair
        (Primrec.pair graph edge) edgeIndex)
  exact (Primrec.list_map tagged route).of_eq fun _ => rfl

theorem drawing_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawing : PeriodicGraph Vertex → PeriodicGridDrawing) := by
  have gridSizePred : Primrec fun graph : PeriodicGraph Vertex =>
      drawingGridSize graph - 1 :=
    Primrec.nat_sub.comp drawingGridSize_primrec (Primrec.const 1)
  have data : Primrec fun graph : PeriodicGraph Vertex =>
      (drawingGridSize graph - 1,
        constructedVertexPositions graph,
        constructedEdgeRoutes graph) :=
    Primrec.pair gridSizePred
      (Primrec.pair constructedVertexPositions_primrec
        constructedEdgeRoutes_primrec)
  exact (PeriodicGridDrawing.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem drawing_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (drawing : PeriodicGraph Vertex → PeriodicGridDrawing) :=
  drawing_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes

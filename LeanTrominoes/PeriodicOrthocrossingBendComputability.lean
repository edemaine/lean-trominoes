import LeanTrominoes.PeriodicCNFPlanarRetainedFormula
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierFormulaComputability

/-!
# Computability of route-bend equalities

The retained planar-SAT formula combines its straight carrier clauses with
one equality gadget at every bend of every neighboring route occurrence.
This module gives route bends their standard encoding and proves the bend
enumeration, equality links, and positioned bend formula primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

namespace RouteBend

def equivData : RouteBend ≃
    (Nat × Nat) × (Cell × (Cell × (Cell × Cell))) where
  toFun bend :=
    ((bend.routeIndex, bend.incomingSegmentIndex),
      (bend.translate,
        (bend.incomingStart, (bend.bend, bend.outgoingFinish))))
  invFun data :=
    ⟨data.1.1, data.1.2, data.2.1,
      data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
  left_inv bend := by cases bend; rfl
  right_inv data := by
    rcases data with ⟨⟨routeIndex, incomingSegmentIndex⟩,
      translate, incomingStart, bend, outgoingFinish⟩
    rfl

noncomputable instance : Primcodable RouteBend :=
  Primcodable.ofEquiv
    ((Nat × Nat) × (Cell × (Cell × (Cell × Cell)))) equivData

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec : Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem routeIndex_primrec : Primrec RouteBend.routeIndex :=
  ((Primrec.fst.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem incomingSegmentIndex_primrec :
    Primrec RouteBend.incomingSegmentIndex :=
  ((Primrec.snd.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem translate_primrec : Primrec RouteBend.translate :=
  ((Primrec.fst.comp Primrec.snd).comp equivData_primrec).of_eq
    fun _ => rfl

theorem incomingStart_primrec : Primrec RouteBend.incomingStart :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

theorem bend_primrec : Primrec RouteBend.bend :=
  ((Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
      equivData_primrec).of_eq fun _ => rfl

theorem outgoingFinish_primrec : Primrec RouteBend.outgoingFinish :=
  ((Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp
      equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec : Primrec fun data :
    (Nat × Nat) × (Cell × (Cell × (Cell × Cell))) =>
    RouteBend.mk data.1.1 data.1.2 data.2.1
      data.2.2.1 data.2.2.2.1 data.2.2.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

theorem incomingTerminal_primrec : Primrec RouteBend.incomingTerminal := by
  have segment : Primrec fun routeBend : RouteBend =>
      GridSegment.mk routeBend.incomingStart routeBend.bend :=
    GridSegment.mk_primrec.comp incomingStart_primrec bend_primrec
  have indexed : Primrec fun routeBend : RouteBend =>
      IndexedGridSegment.mk routeBend.routeIndex
        routeBend.incomingSegmentIndex
        (GridSegment.mk routeBend.incomingStart routeBend.bend) :=
    IndexedGridSegment.mk_primrec.comp
      (Primrec.pair routeIndex_primrec
        (Primrec.pair incomingSegmentIndex_primrec segment))
  exact (SegmentTerminal.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair indexed translate_primrec)
      (Primrec.const SegmentEnd.finish))).of_eq fun _ => rfl

theorem outgoingTerminal_primrec : Primrec RouteBend.outgoingTerminal := by
  have segment : Primrec fun routeBend : RouteBend =>
      GridSegment.mk routeBend.bend routeBend.outgoingFinish :=
    GridSegment.mk_primrec.comp bend_primrec outgoingFinish_primrec
  have segmentIndex : Primrec fun routeBend : RouteBend =>
      routeBend.incomingSegmentIndex + 1 :=
    Primrec.nat_add.comp incomingSegmentIndex_primrec (Primrec.const 1)
  have indexed : Primrec fun routeBend : RouteBend =>
      IndexedGridSegment.mk routeBend.routeIndex
        (routeBend.incomingSegmentIndex + 1)
        (GridSegment.mk routeBend.bend routeBend.outgoingFinish) :=
    IndexedGridSegment.mk_primrec.comp
      (Primrec.pair routeIndex_primrec
        (Primrec.pair segmentIndex segment))
  exact (SegmentTerminal.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair indexed translate_primrec)
      (Primrec.const SegmentEnd.start))).of_eq fun _ => rfl

end RouteBend

private abbrev RouteBendWindow := (Cell × Cell) × (Cell × Cell)

private def routeBendWindows (route : List Cell) :
    List RouteBendWindow :=
  consecutivePairs (consecutivePairs route)

private def routeBendOfTaggedWindow (routeIndex : Nat)
    (translate : Cell) (tagged : RouteBendWindow × Nat) : RouteBend :=
  ⟨routeIndex, tagged.2, translate,
    tagged.1.1.1, tagged.1.1.2, tagged.1.2.2⟩

private theorem routeBendsAux_eq_taggedWindows
    (routeIndex : Nat) (translate : Cell)
    (incomingSegmentIndex : Nat) (route : List Cell) :
    routeBendsAux routeIndex translate incomingSegmentIndex route =
      ((routeBendWindows route).zipIdx incomingSegmentIndex).map
        (routeBendOfTaggedWindow routeIndex translate) := by
  induction route generalizing incomingSegmentIndex with
  | nil => rfl
  | cons incomingStart rest induction =>
      cases rest with
      | nil => rfl
      | cons bend rest =>
          cases rest with
          | nil => rfl
          | cons outgoingFinish tail =>
              simp only [routeBendsAux, routeBendWindows,
                consecutivePairs, List.zipIdx_cons, List.map_cons,
                routeBendOfTaggedWindow]
              exact congrArg
                (List.cons
                  { routeIndex := routeIndex
                    incomingSegmentIndex := incomingSegmentIndex
                    translate := translate
                    incomingStart := incomingStart
                    bend := bend
                    outgoingFinish := outgoingFinish })
                (induction (incomingSegmentIndex + 1))

private theorem routeBends_eq_taggedWindows
    (routeIndex : Nat) (translate : Cell) (route : List Cell) :
    routeBends routeIndex translate route =
      (routeBendWindows route).zipIdx.map
        (routeBendOfTaggedWindow routeIndex translate) := by
  exact routeBendsAux_eq_taggedWindows routeIndex translate 0 route

theorem routeBends_primrec :
    Primrec fun input : (Nat × Cell) × List Cell =>
      routeBends input.1.1 input.1.2 input.2 := by
  have windows : Primrec fun input : (Nat × Cell) × List Cell =>
      routeBendWindows input.2 :=
    consecutivePairs_primrec.comp
      (consecutivePairs_primrec.comp Primrec.snd)
  have tagged : Primrec fun input : (Nat × Cell) × List Cell =>
      (routeBendWindows input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp windows
  have one : Primrec₂ fun (input : (Nat × Cell) × List Cell)
      (window : RouteBendWindow × Nat) =>
      routeBendOfTaggedWindow input.1.1 input.1.2 window := by
    change Primrec fun combined :
        ((Nat × Cell) × List Cell) × (RouteBendWindow × Nat) =>
      RouteBend.mk combined.1.1.1 combined.2.2 combined.1.1.2
        combined.2.1.1.1 combined.2.1.1.2 combined.2.1.2.2
    exact RouteBend.mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd))
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
            (Primrec.pair
              (Primrec.snd.comp
                (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
              (Primrec.snd.comp
                (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))))
  exact (Primrec.list_map tagged one).of_eq fun input =>
    (routeBends_eq_taggedWindows input.1.1 input.1.2 input.2).symm

theorem drawingRouteBends_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingRouteBends :
      PeriodicGraph Vertex → List RouteBend) := by
  have taggedRoutes : Primrec fun graph : PeriodicGraph Vertex =>
      (drawing graph).edgeRoutes.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicGridDrawing.edgeRoutes_primrec.comp drawing_primrec)
  have translated : Primrec₂ fun
      (graph : PeriodicGraph Vertex) (taggedRoute : List Cell × Nat) =>
      neighborTranslations.flatMap fun translate =>
        routeBends taggedRoute.2 translate taggedRoute.1 := by
    change Primrec fun input :
        PeriodicGraph Vertex × (List Cell × Nat) =>
      neighborTranslations.flatMap fun translate =>
        routeBends input.2.2 translate input.2.1
    have one : Primrec₂ fun
        (input : PeriodicGraph Vertex × (List Cell × Nat))
        (translate : Cell) =>
        routeBends input.2.2 translate input.2.1 := by
      change Primrec fun combined :
          (PeriodicGraph Vertex × (List Cell × Nat)) × Cell =>
        routeBends combined.1.2.2 combined.2 combined.1.2.1
      exact routeBends_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    exact Primrec.list_flatMap (Primrec.const neighborTranslations) one
  exact Primrec.list_flatMap taggedRoutes translated

theorem RouteBend.drawingPoint_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      input.2.drawingPoint input.1 := by
  have drawing : Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      PeriodicOrthocrossing.drawing input.1 :=
    drawing_primrec.comp Primrec.fst
  have translation : Primrec fun input :
      PeriodicGraph Vertex × RouteBend =>
      (PeriodicOrthocrossing.drawing input.1).periodTranslation
        input.2.translate :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      drawing (RouteBend.translate_primrec.comp Primrec.snd)
  exact Computability.cell_add_primrec.comp translation
    (RouteBend.bend_primrec.comp Primrec.snd)

theorem routeBendEqualityPositions_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      routeBendEqualityPositions input.1 input.2 := by
  have origin : Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      Cell.scale planarMacroScale (input.2.drawingPoint input.1) :=
    Computability.cell_scale_primrec.comp
      (Primrec.const planarMacroScale)
      RouteBend.drawingPoint_primrec
  exact (EqualityPositions.mk_primrec.comp
    (Primrec.pair
      (Computability.cell_add_primrec.comp origin (Primrec.const (5, 5)))
      (Computability.cell_add_primrec.comp origin
        (Primrec.const (8, 8))))).of_eq fun _ => rfl

theorem RouteBend.equalityLink_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      input.2.equalityLink input.1 := by
  have first : Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      CarrierNode.terminal input.2.incomingTerminal :=
    CarrierNode.terminal_primrec.comp
      (RouteBend.incomingTerminal_primrec.comp Primrec.snd)
  have second : Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      CarrierNode.terminal input.2.outgoingTerminal :=
    CarrierNode.terminal_primrec.comp
      (RouteBend.outgoingTerminal_primrec.comp Primrec.snd)
  exact (EqualityLink.mk_primrec.comp
    (Primrec.pair (Primrec.pair first second)
      routeBendEqualityPositions_primrec)).of_eq fun _ => rfl

theorem drawingRouteBendLinks_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingRouteBendLinks :
      PeriodicGraph Vertex → List (EqualityLink CarrierNode)) := by
  have bends : Primrec fun graph : PeriodicGraph Vertex =>
      (drawingRouteBends graph).dedup :=
    PeriodicThreeSATThree.dedup_primrec.comp drawingRouteBends_primrec
  exact Primrec.list_map bends
    (RouteBend.equalityLink_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂

theorem drawingRouteBendFormula_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingRouteBendFormula :
      PeriodicGraph Vertex → List (EmbeddedClause CarrierNode)) :=
  equalityFamily_primrec.comp drawingRouteBendLinks_primrec

theorem drawingRouteBendFormula_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (drawingRouteBendFormula :
      PeriodicGraph Vertex → List (EmbeddedClause CarrierNode)) :=
  drawingRouteBendFormula_primrec.to_comp

/-- The retained straight carriers and route-bend equalities together form
a primitive-recursive wire formula. -/
theorem retainedDrawingRouteWireFormula_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingRouteWireFormula :
      PeriodicGraph Vertex → List (EmbeddedClause CarrierNode)) :=
  Primrec.list_append.comp
    retainedDrawingCompleteCarrierFormula_primrec
    drawingRouteBendFormula_primrec

theorem retainedDrawingRouteWireFormula_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (retainedDrawingRouteWireFormula :
      PeriodicGraph Vertex → List (EmbeddedClause CarrierNode)) :=
  retainedDrawingRouteWireFormula_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes

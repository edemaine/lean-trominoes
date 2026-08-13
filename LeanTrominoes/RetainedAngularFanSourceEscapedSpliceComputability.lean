/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedRayRasterizationComputability

/-!
# Computability of source-escaped retained fan splices

The exceptional fallback branch delays its occurrence-lane shift for a fixed
number of retained-ray blocks, follows the remaining radial ray, traverses a
finite fan adapter, replaces the old variable-side route tail, and finally
rasterizes the whole retained-ray polyline.  This module proves each of those
operations primitive recursive and assembles the exact generic escaped
boundary route.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT
open LeanTrominoes.Computability

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ## Generic list and scaling operations -/

theorem scalePolylineQuery_primrec :
    Primrec fun input : Int × List Cell =>
      scalePolyline input.1 input.2 := by
  have scaledPoint : Primrec₂ fun (input : Int × List Cell)
      (point : Cell) => Cell.scale input.1 point :=
    cell_scale_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact (Primrec.list_map Primrec.snd scaledPoint).of_eq fun _ => rfl

theorem scaleRetainedTerminalData_primrec :
    Primrec fun input : Nat × RetainedTerminalData =>
      scaleRetainedTerminalData input.1 input.2 := by
  exact (Primrec.pair
    (Primrec.fst.comp Primrec.snd)
    (Primrec.nat_mul.comp Primrec.fst
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

theorem replacePolylineTail_primrec
    {alpha : Type*} [Primcodable alpha] :
    Primrec fun input : List alpha × List alpha =>
      replacePolylineTail input.1 input.2 := by
  have reversedReplacement : Primrec fun input :
      List alpha × List alpha => input.2.reverse :=
    Primrec.list_reverse.comp Primrec.snd
  have reversedRoute : Primrec fun input :
      List alpha × List alpha => input.1.reverse :=
    Primrec.list_reverse.comp Primrec.fst
  have replacedHead : Primrec fun input : List alpha × List alpha =>
      replacePolylineHead input.2.reverse input.1.reverse := by
    have routeTail := Primrec.list_tail.comp reversedRoute
    exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
      reversedReplacement routeTail).of_eq fun _ => rfl
  exact (Primrec.list_reverse.comp replacedHead).of_eq fun _ => rfl

theorem polylineGetLastD_primrec :
    Primrec fun route : List Cell => route.getLastD (0, 0) := by
  have last : Primrec fun route : List Cell => route.reverse.head? :=
    Primrec.list_head?.comp (Primrec.list_reverse.comp Primrec.id)
  exact (Primrec.option_getD.comp last
    (Primrec.const ((0, 0) : Cell))).of_eq fun route => by simp

/-! ## Finite fan geometry and retained-ray data -/

theorem retainedTerminalDirection_primitive_primrec :
    Primrec RetainedTerminalDirection.primitive :=
  Primrec.dom_finite _

theorem retainedTerminalInterfaceMultiplier_primrec :
    Primrec retainedTerminalInterfaceMultiplier :=
  Primrec.dom_finite _

theorem retainedTerminalFanOuterLaneOffset_primrec :
    Primrec fun input :
        RetainedTerminalDirection × RetainedTerminalSlot =>
      retainedTerminalFanOuterLaneOffset input.1 input.2 :=
  Primrec.dom_finite _

theorem retainedTerminalFanOuterLaneShiftRoute_primrec :
    Primrec fun input :
        RetainedTerminalDirection × RetainedTerminalSlot =>
      retainedTerminalFanOuterLaneShiftRoute input.1 input.2 :=
  Primrec.dom_finite _

theorem retainedTerminalFanOuterLocalRoute_primrec :
    Primrec fun input :
        RetainedTerminalDirection × RetainedTerminalSlot =>
      retainedTerminalFanOuterLocalRoute input.1 input.2 :=
  Primrec.dom_finite _

theorem retainedTerminalFanOuterRadialLength_primrec :
    Primrec retainedTerminalFanOuterRadialLength := by
  have total : Primrec fun terminal : RetainedTerminalData =>
      retainedTerminalFanTotalRefinement * terminal.2 :=
    Primrec.nat_mul.comp
      (Primrec.const retainedTerminalFanTotalRefinement) Primrec.snd
  have interface : Primrec fun terminal : RetainedTerminalData =>
      retainedTerminalFanRoutingRefinement *
        retainedTerminalInterfaceMultiplier terminal.1 :=
    Primrec.nat_mul.comp
      (Primrec.const retainedTerminalFanRoutingRefinement)
      (retainedTerminalInterfaceMultiplier_primrec.comp Primrec.fst)
  exact (Primrec.nat_sub.comp total interface).of_eq fun _ => rfl

theorem retainedTerminalFanOuterInwardRayOfLength_primrec :
    Primrec fun input : RetainedTerminalDirection × Nat =>
      retainedTerminalFanOuterInwardRayOfLength input.1 input.2 := by
  have encoded : Primrec fun input : RetainedTerminalDirection × Nat =>
      RetainedTerminalDirection.equivData input.1 :=
    RetainedTerminalDirection.equivData_primrec.comp Primrec.fst
  have compass : Primrec₂ fun
      (input : RetainedTerminalDirection × Nat) (port : Port) =>
      RetainedRay.compass (oppositePort port) input.2 := by
    have data : Primrec fun input :
        (RetainedTerminalDirection × Nat) × Port =>
        (oppositePort input.2, input.1.2) :=
      Primrec.pair
        (oppositePort_primrec.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    exact (RetainedRay.compass_primrec.comp data).to₂
  have routed : Primrec₂ fun
      (input : RetainedTerminalDirection × Nat) (arm : DuplicatorArm) =>
      RetainedRay.routedClause arm input.2 := by
    have data : Primrec fun input :
        (RetainedTerminalDirection × Nat) × DuplicatorArm =>
        (input.2, input.1.2) :=
      Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)
    exact (RetainedRay.routedClause_primrec.comp data).to₂
  exact (Primrec.sumCasesOn encoded compass routed).of_eq fun input => by
    cases input.1 <;> rfl

theorem retainedTerminalFanOuterInwardRay_primrec :
    Primrec retainedTerminalFanOuterInwardRay := by
  exact (retainedTerminalFanOuterInwardRayOfLength_primrec.comp
    (Primrec.pair Primrec.fst
      retainedTerminalFanOuterRadialLength_primrec)).of_eq fun terminal => by
        rcases terminal with ⟨direction, length⟩
        cases direction <;> rfl

theorem retainedTerminalFanOuterSourceEscapeRay_primrec :
    Primrec retainedTerminalFanOuterSourceEscapeRay := by
  exact (retainedTerminalFanOuterInwardRayOfLength_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.const retainedTerminalFanOuterSourceEscapeLength))).of_eq
        fun _ => rfl

theorem retainedTerminalFanOuterEscapedRemainingRay_primrec :
    Primrec retainedTerminalFanOuterEscapedRemainingRay := by
  have remaining : Primrec fun terminal : RetainedTerminalData =>
      retainedTerminalFanOuterRadialLength terminal -
        retainedTerminalFanOuterSourceEscapeLength :=
    Primrec.nat_sub.comp retainedTerminalFanOuterRadialLength_primrec
      (Primrec.const retainedTerminalFanOuterSourceEscapeLength)
  exact (retainedTerminalFanOuterInwardRayOfLength_primrec.comp
    (Primrec.pair Primrec.fst remaining)).of_eq fun _ => rfl

theorem RetainedRay.vector_primrec : Primrec RetainedRay.vector := by
  have encoded := RetainedRay.equivData_primrec
  have compass : Primrec₂ fun (_ray : RetainedRay)
      (data : Port × Nat) =>
      Cell.scale data.2 data.1.unitVector := by
    have unit : Primrec fun input : RetainedRay × (Port × Nat) =>
        input.2.1.unitVector :=
      (Primrec.dom_finite Port.unitVector).comp
        (Primrec.fst.comp Primrec.snd)
    exact (cell_scale_primrec.comp
      (int_ofNat_primrec.comp (Primrec.snd.comp Primrec.snd))
      unit).to₂
  have routed : Primrec₂ fun (_ray : RetainedRay)
      (data : DuplicatorArm × Nat) =>
      Cell.scale data.2 (routedClauseRayPrimitive data.1) := by
    exact (cell_scale_primrec.comp
      (int_ofNat_primrec.comp (Primrec.snd.comp Primrec.snd))
      (routedClauseRayPrimitive_primrec.comp
        (Primrec.fst.comp Primrec.snd))).to₂
  exact (Primrec.sumCasesOn encoded compass routed).of_eq fun ray => by
    cases ray <;> rfl

private theorem retainedTerminalSplicePoint_primrec :
    Primrec fun input : Cell × RetainedTerminalData =>
      retainedTerminalSplicePoint input.1 input.2 := by
  have scaled : Primrec fun input : Cell × RetainedTerminalData =>
      Cell.scale input.2.2 input.2.1.primitive :=
    cell_scale_primrec.comp
      (int_ofNat_primrec.comp (Primrec.snd.comp Primrec.snd))
      (retainedTerminalDirection_primitive_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  exact (cell_add_primrec.comp Primrec.fst scaled).of_eq fun _ => rfl

/-! ## Ordinary outer fan route -/

abbrev RetainedFanQuery :=
  (Cell × RetainedTerminalData) × RetainedTerminalSlot

private def retainedFanGateQuery
    (input : RetainedFanQuery) : Cell :=
  (retainedAngularFanOuterDemand input.1.1 input.1.2 input.2).gate

private theorem retainedFanGateQuery_primrec :
    Primrec retainedFanGateQuery := by
  have scaledTerminal : Primrec fun input : RetainedFanQuery =>
      scaleRetainedTerminalData retainedTerminalFanTotalRefinement
        input.1.2 :=
    scaleRetainedTerminalData_primrec.comp
      (Primrec.pair
        (Primrec.const retainedTerminalFanTotalRefinement)
        (Primrec.snd.comp Primrec.fst))
  exact (retainedTerminalSplicePoint_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      scaledTerminal)).of_eq fun _ => rfl

private def retainedFanShiftedGateQuery
    (input : RetainedFanQuery) : Cell :=
  Cell.add
    (retainedFanGateQuery input)
    (retainedTerminalFanOuterLaneOffset input.1.2.1 input.2)

private theorem retainedFanShiftedGateQuery_primrec :
    Primrec retainedFanShiftedGateQuery := by
  have offset : Primrec fun input : RetainedFanQuery =>
      retainedTerminalFanOuterLaneOffset input.1.2.1 input.2 :=
    retainedTerminalFanOuterLaneOffset_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  exact cell_add_primrec.comp retainedFanGateQuery_primrec offset

private def retainedFanLaneShiftQuery
    (input : RetainedFanQuery) : List Cell :=
  retainedTerminalFanOuterLaneShiftRouteAt
    (retainedFanGateQuery input)
    input.1.2.1 input.2

private theorem retainedFanLaneShiftQuery_primrec :
    Primrec retainedFanLaneShiftQuery := by
  have template : Primrec fun input : RetainedFanQuery =>
      retainedTerminalFanOuterLaneShiftRoute input.1.2.1 input.2 :=
    retainedTerminalFanOuterLaneShiftRoute_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have translated : Primrec₂ fun
      (input : RetainedFanQuery) (point : Cell) =>
      Cell.add (retainedFanGateQuery input) point :=
    cell_add_primrec.comp₂
      (retainedFanGateQuery_primrec.comp₂ Primrec₂.left)
      Primrec₂.right
  exact (Primrec.list_map template translated).of_eq fun _ => rfl

private def retainedFanInwardRasterQuery
    (input : RetainedFanQuery) : List Cell :=
  (retainedTerminalFanOuterInwardRay input.1.2).rasterize
    (retainedFanShiftedGateQuery input)

private theorem retainedFanInwardRasterQuery_primrec :
    Primrec retainedFanInwardRasterQuery := by
  have ray : Primrec fun input : RetainedFanQuery =>
      retainedTerminalFanOuterInwardRay input.1.2 :=
    retainedTerminalFanOuterInwardRay_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  exact (RetainedRay.rasterize_primrec.comp
    (Primrec.pair ray retainedFanShiftedGateQuery_primrec)).of_eq
      fun _ => rfl

private def retainedFanRadialRouteQuery
    (input : RetainedFanQuery) : List Cell :=
  retainedTerminalFanOuterRadialRoute
    input.1.1 input.1.2 input.2

private theorem retainedFanRadialRouteQuery_primrec :
    Primrec retainedFanRadialRouteQuery := by
  exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
    retainedFanLaneShiftQuery_primrec
    retainedFanInwardRasterQuery_primrec).of_eq fun _ => rfl

private def retainedFanLocalRouteQuery
    (input : RetainedFanQuery) : List Cell :=
  retainedTerminalFanOuterLocalRouteAt
    input.1.1 input.1.2.1 input.2

private theorem retainedFanLocalRouteQuery_primrec :
    Primrec retainedFanLocalRouteQuery := by
  have template : Primrec fun input : RetainedFanQuery =>
      retainedTerminalFanOuterLocalRoute input.1.2.1 input.2 :=
    retainedTerminalFanOuterLocalRoute_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have translated : Primrec₂ fun
      (input : RetainedFanQuery) (point : Cell) =>
      Cell.add input.1.1 point :=
    cell_add_primrec.comp₂
      ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left)
      Primrec₂.right
  exact (Primrec.list_map template translated).of_eq fun _ => rfl

def retainedTerminalFanOuterCompleteRouteQuery
    (input : RetainedFanQuery) : List Cell :=
  retainedTerminalFanOuterCompleteRoute
    input.1.1 input.1.2 input.2

theorem retainedTerminalFanOuterCompleteRouteQuery_primrec :
    Primrec retainedTerminalFanOuterCompleteRouteQuery := by
  exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
    retainedFanRadialRouteQuery_primrec
    retainedFanLocalRouteQuery_primrec).of_eq fun _ => rfl

/-! ## Escaped outer fan route -/

abbrev RetainedEscapedFanQuery := RetainedFanQuery

private def retainedAngularFanOuterDemandGateQuery
    (input : RetainedEscapedFanQuery) : Cell :=
  (retainedAngularFanOuterDemand input.1.1 input.1.2 input.2).gate

private theorem retainedAngularFanOuterDemandGateQuery_primrec :
    Primrec retainedAngularFanOuterDemandGateQuery := by
  have scaledTerminal : Primrec fun input : RetainedEscapedFanQuery =>
      scaleRetainedTerminalData retainedTerminalFanTotalRefinement
        input.1.2 :=
    scaleRetainedTerminalData_primrec.comp
      (Primrec.pair
        (Primrec.const retainedTerminalFanTotalRefinement)
        (Primrec.snd.comp Primrec.fst))
  exact (retainedTerminalSplicePoint_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      scaledTerminal)).of_eq fun _ => rfl

private def retainedEscapedFanSourceRayQuery
    (input : RetainedEscapedFanQuery) : RetainedRay :=
  retainedTerminalFanOuterSourceEscapeRay input.1.2

private theorem retainedEscapedFanSourceRayQuery_primrec :
    Primrec retainedEscapedFanSourceRayQuery :=
  retainedTerminalFanOuterSourceEscapeRay_primrec.comp
    (Primrec.snd.comp Primrec.fst)

private def retainedEscapedFanSourceEscapePointQuery
    (input : RetainedEscapedFanQuery) : Cell :=
  retainedTerminalFanOuterSourceEscapePoint
    input.1.1 input.1.2 input.2

private theorem retainedEscapedFanSourceEscapePointQuery_primrec :
    Primrec retainedEscapedFanSourceEscapePointQuery := by
  exact (cell_add_primrec.comp
    retainedAngularFanOuterDemandGateQuery_primrec
    (RetainedRay.vector_primrec.comp
      retainedEscapedFanSourceRayQuery_primrec)).of_eq fun _ => rfl

private def retainedEscapedFanShiftedEscapePointQuery
    (input : RetainedEscapedFanQuery) : Cell :=
  Cell.add
    (retainedEscapedFanSourceEscapePointQuery input)
    (retainedTerminalFanOuterLaneOffset input.1.2.1 input.2)

private theorem retainedEscapedFanShiftedEscapePointQuery_primrec :
    Primrec retainedEscapedFanShiftedEscapePointQuery := by
  have offset : Primrec fun input : RetainedEscapedFanQuery =>
      retainedTerminalFanOuterLaneOffset input.1.2.1 input.2 :=
    retainedTerminalFanOuterLaneOffset_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  exact cell_add_primrec.comp
    retainedEscapedFanSourceEscapePointQuery_primrec offset

private def retainedEscapedFanSourceRasterQuery
    (input : RetainedEscapedFanQuery) : List Cell :=
  (retainedTerminalFanOuterSourceEscapeRay input.1.2).rasterize
    (retainedAngularFanOuterDemand input.1.1 input.1.2 input.2).gate

private theorem retainedEscapedFanSourceRasterQuery_primrec :
    Primrec retainedEscapedFanSourceRasterQuery := by
  exact (RetainedRay.rasterize_primrec.comp
    (Primrec.pair retainedEscapedFanSourceRayQuery_primrec
      retainedAngularFanOuterDemandGateQuery_primrec)).of_eq fun _ => rfl

private def retainedEscapedFanLaneShiftQuery
    (input : RetainedEscapedFanQuery) : List Cell :=
  retainedTerminalFanOuterLaneShiftRouteAt
    (retainedEscapedFanSourceEscapePointQuery input)
    input.1.2.1 input.2

private theorem retainedEscapedFanLaneShiftQuery_primrec :
    Primrec retainedEscapedFanLaneShiftQuery := by
  have template : Primrec fun input : RetainedEscapedFanQuery =>
      retainedTerminalFanOuterLaneShiftRoute input.1.2.1 input.2 :=
    retainedTerminalFanOuterLaneShiftRoute_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have translated : Primrec₂ fun
      (input : RetainedEscapedFanQuery) (point : Cell) =>
      Cell.add (retainedEscapedFanSourceEscapePointQuery input) point :=
    cell_add_primrec.comp₂
      (retainedEscapedFanSourceEscapePointQuery_primrec.comp₂
        Primrec₂.left)
      Primrec₂.right
  exact (Primrec.list_map template translated).of_eq fun _ => rfl

private def retainedEscapedFanRemainingRasterQuery
    (input : RetainedEscapedFanQuery) : List Cell :=
  (retainedTerminalFanOuterEscapedRemainingRay input.1.2).rasterize
    (retainedEscapedFanShiftedEscapePointQuery input)

private theorem retainedEscapedFanRemainingRasterQuery_primrec :
    Primrec retainedEscapedFanRemainingRasterQuery := by
  have ray : Primrec fun input : RetainedEscapedFanQuery =>
      retainedTerminalFanOuterEscapedRemainingRay input.1.2 :=
    retainedTerminalFanOuterEscapedRemainingRay_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  exact (RetainedRay.rasterize_primrec.comp
    (Primrec.pair ray
      retainedEscapedFanShiftedEscapePointQuery_primrec)).of_eq fun _ => rfl

private def retainedEscapedFanRadialRouteQuery
    (input : RetainedEscapedFanQuery) : List Cell :=
  retainedTerminalFanOuterEscapedRadialRoute
    input.1.1 input.1.2 input.2

private theorem retainedEscapedFanRadialRouteQuery_primrec :
    Primrec retainedEscapedFanRadialRouteQuery := by
  have shiftedRemaining : Primrec fun input : RetainedEscapedFanQuery =>
      joinAtEndpoint
        (retainedEscapedFanLaneShiftQuery input)
        (retainedEscapedFanRemainingRasterQuery input) :=
    PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
      retainedEscapedFanLaneShiftQuery_primrec
      retainedEscapedFanRemainingRasterQuery_primrec
  exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
    retainedEscapedFanSourceRasterQuery_primrec
    shiftedRemaining).of_eq fun _ => rfl

private def retainedEscapedFanLocalRouteQuery
    (input : RetainedEscapedFanQuery) : List Cell :=
  retainedTerminalFanOuterLocalRouteAt
    input.1.1 input.1.2.1 input.2

private theorem retainedEscapedFanLocalRouteQuery_primrec :
    Primrec retainedEscapedFanLocalRouteQuery := by
  have template : Primrec fun input : RetainedEscapedFanQuery =>
      retainedTerminalFanOuterLocalRoute input.1.2.1 input.2 :=
    retainedTerminalFanOuterLocalRoute_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have translated : Primrec₂ fun
      (input : RetainedEscapedFanQuery) (point : Cell) =>
      Cell.add input.1.1 point :=
    cell_add_primrec.comp₂
      ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left)
      Primrec₂.right
  exact (Primrec.list_map template translated).of_eq fun _ => rfl

def retainedTerminalFanOuterEscapedCompleteRouteQuery
    (input : RetainedEscapedFanQuery) : List Cell :=
  retainedTerminalFanOuterEscapedCompleteRoute
    input.1.1 input.1.2 input.2

theorem retainedTerminalFanOuterEscapedCompleteRouteQuery_primrec :
    Primrec retainedTerminalFanOuterEscapedCompleteRouteQuery := by
  exact (PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
    retainedEscapedFanRadialRouteQuery_primrec
    retainedEscapedFanLocalRouteQuery_primrec).of_eq fun _ => rfl

/-! ## Tail replacement and final boundary rasterization -/

abbrev RetainedEscapedBoundaryQuery :=
  (List Cell × RetainedTerminalData) × RetainedTerminalSlot

private def retainedEscapedBoundaryCenterQuery
    (input : RetainedEscapedBoundaryQuery) : Cell :=
  Cell.scale retainedTerminalFanTotalRefinement
    (input.1.1.getLastD (0, 0))

private theorem retainedEscapedBoundaryCenterQuery_primrec :
    Primrec retainedEscapedBoundaryCenterQuery := by
  exact cell_scale_primrec.comp
    (Primrec.const (retainedTerminalFanTotalRefinement : Int))
    (polylineGetLastD_primrec.comp
      (Primrec.fst.comp Primrec.fst))

private def retainedEscapedBoundaryScaledRouteQuery
    (input : RetainedEscapedBoundaryQuery) : List Cell :=
  scalePolyline retainedTerminalFanTotalRefinement input.1.1

private theorem retainedEscapedBoundaryScaledRouteQuery_primrec :
    Primrec retainedEscapedBoundaryScaledRouteQuery := by
  exact scalePolylineQuery_primrec.comp
    (Primrec.pair
      (Primrec.const (retainedTerminalFanTotalRefinement : Int))
      (Primrec.fst.comp Primrec.fst))

private def retainedEscapedBoundaryReplacementQuery
    (input : RetainedEscapedBoundaryQuery) : List Cell :=
  retainedTerminalFanOuterEscapedCompleteRoute
    (retainedEscapedBoundaryCenterQuery input) input.1.2 input.2

private theorem retainedEscapedBoundaryReplacementQuery_primrec :
    Primrec retainedEscapedBoundaryReplacementQuery := by
  exact (retainedTerminalFanOuterEscapedCompleteRouteQuery_primrec.comp
    (Primrec.pair
      (Primrec.pair retainedEscapedBoundaryCenterQuery_primrec
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)).of_eq fun _ => rfl

def retainedAngularFanEscapedSplicedBoundaryPolylineQuery
    (input : RetainedEscapedBoundaryQuery) : List Cell :=
  retainedAngularFanEscapedSplicedBoundaryPolyline
    input.1.1 input.1.2 input.2

theorem retainedAngularFanEscapedSplicedBoundaryPolylineQuery_primrec :
    Primrec retainedAngularFanEscapedSplicedBoundaryPolylineQuery := by
  exact (replacePolylineTail_primrec.comp
    (Primrec.pair retainedEscapedBoundaryScaledRouteQuery_primrec
      retainedEscapedBoundaryReplacementQuery_primrec)).of_eq fun _ => rfl

def retainedAngularFanEscapedSplicedBoundaryRouteQuery
    (input : RetainedEscapedBoundaryQuery) : List Cell :=
  retainedAngularFanEscapedSplicedBoundaryRoute
    input.1.1 input.1.2 input.2

theorem retainedAngularFanEscapedSplicedBoundaryRouteQuery_primrec :
    Primrec retainedAngularFanEscapedSplicedBoundaryRouteQuery := by
  exact (rasterizeRetainedPolyline_primrec.comp
    retainedAngularFanEscapedSplicedBoundaryPolylineQuery_primrec).of_eq
      fun _ => rfl

/-! ## Ordinary tail replacement and final boundary rasterization -/

abbrev RetainedBoundaryQuery :=
  (List Cell × RetainedTerminalData) × RetainedTerminalSlot

private def retainedBoundaryReplacementQuery
    (input : RetainedBoundaryQuery) : List Cell :=
  retainedTerminalFanOuterCompleteRoute
    (retainedEscapedBoundaryCenterQuery input) input.1.2 input.2

private theorem retainedBoundaryReplacementQuery_primrec :
    Primrec retainedBoundaryReplacementQuery := by
  exact (retainedTerminalFanOuterCompleteRouteQuery_primrec.comp
    (Primrec.pair
      (Primrec.pair retainedEscapedBoundaryCenterQuery_primrec
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)).of_eq fun _ => rfl

def retainedAngularFanSplicedBoundaryPolylineQuery
    (input : RetainedBoundaryQuery) : List Cell :=
  retainedAngularFanSplicedBoundaryPolyline
    input.1.1 input.1.2 input.2

theorem retainedAngularFanSplicedBoundaryPolylineQuery_primrec :
    Primrec retainedAngularFanSplicedBoundaryPolylineQuery := by
  exact (replacePolylineTail_primrec.comp
    (Primrec.pair retainedEscapedBoundaryScaledRouteQuery_primrec
      retainedBoundaryReplacementQuery_primrec)).of_eq fun _ => rfl

def retainedAngularFanSplicedBoundaryRouteQuery
    (input : RetainedBoundaryQuery) : List Cell :=
  retainedAngularFanSplicedBoundaryRoute
    input.1.1 input.1.2 input.2

theorem retainedAngularFanSplicedBoundaryRouteQuery_primrec :
    Primrec retainedAngularFanSplicedBoundaryRouteQuery := by
  exact (rasterizeRetainedPolyline_primrec.comp
    retainedAngularFanSplicedBoundaryPolylineQuery_primrec).of_eq
      fun _ => rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes

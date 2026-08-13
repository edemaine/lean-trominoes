/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATComputability
import LeanTrominoes.PeriodicOrthocrossingBendComputability

/-!
# Computability of the retained crossover-and-wire core

The fixed Figure 8 crossover is instantiated at each canonical crossing.
This module proves the carrier-node ports, macrocell origins, scoped gadget
family, and its concatenation with the retained wire formula primitive
recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

private def leftCrossingBoundary (crossing : CrossingRecord) :
    CrossingBoundary :=
  ⟨crossing, .left⟩

private def rightCrossingBoundary (crossing : CrossingRecord) :
    CrossingBoundary :=
  ⟨crossing, .right⟩

private def topCrossingBoundary (crossing : CrossingRecord) :
    CrossingBoundary :=
  ⟨crossing, .top⟩

private def bottomCrossingBoundary (crossing : CrossingRecord) :
    CrossingBoundary :=
  ⟨crossing, .bottom⟩

private theorem leftCrossingBoundary_primrec :
    Primrec leftCrossingBoundary := by
  exact (CrossingBoundary.equivData_symm_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const CrossingSide.left))).of_eq
      fun _ => rfl

private theorem rightCrossingBoundary_primrec :
    Primrec rightCrossingBoundary := by
  exact (CrossingBoundary.equivData_symm_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const CrossingSide.right))).of_eq
      fun _ => rfl

private theorem topCrossingBoundary_primrec :
    Primrec topCrossingBoundary := by
  exact (CrossingBoundary.equivData_symm_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const CrossingSide.top))).of_eq
      fun _ => rfl

private theorem bottomCrossingBoundary_primrec :
    Primrec bottomCrossingBoundary := by
  exact (CrossingBoundary.equivData_symm_primrec.comp
    (Primrec.pair Primrec.id (Primrec.const CrossingSide.bottom))).of_eq
      fun _ => rfl

private def leftCarrierBoundary (crossing : CrossingRecord) : CarrierNode :=
  .boundary (leftCrossingBoundary crossing)

private def rightCarrierBoundary (crossing : CrossingRecord) : CarrierNode :=
  .boundary (rightCrossingBoundary crossing)

private def topCarrierBoundary (crossing : CrossingRecord) : CarrierNode :=
  .boundary (topCrossingBoundary crossing)

private def bottomCarrierBoundary (crossing : CrossingRecord) : CarrierNode :=
  .boundary (bottomCrossingBoundary crossing)

private theorem leftCarrierBoundary_primrec :
    Primrec leftCarrierBoundary :=
  CarrierNode.boundary_primrec.comp leftCrossingBoundary_primrec

private theorem rightCarrierBoundary_primrec :
    Primrec rightCarrierBoundary :=
  CarrierNode.boundary_primrec.comp rightCrossingBoundary_primrec

private theorem topCarrierBoundary_primrec :
    Primrec topCarrierBoundary :=
  CarrierNode.boundary_primrec.comp topCrossingBoundary_primrec

private theorem bottomCarrierBoundary_primrec :
    Primrec bottomCarrierBoundary :=
  CarrierNode.boundary_primrec.comp bottomCrossingBoundary_primrec

theorem carrierNodeCrossingPorts_primrec :
    Primrec carrierNodeCrossingPorts := by
  exact (CrossoverPorts.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair leftCarrierBoundary_primrec
        rightCarrierBoundary_primrec)
      (Primrec.pair topCarrierBoundary_primrec
        bottomCarrierBoundary_primrec))).of_eq fun _ => rfl

theorem crossingPorts_primrec : Primrec crossingPorts := by
  exact (CrossoverPorts.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair leftCrossingBoundary_primrec
        rightCrossingBoundary_primrec)
      (Primrec.pair topCrossingBoundary_primrec
        bottomCrossingBoundary_primrec))).of_eq
        fun _ => rfl

theorem drawingCrossoverFormula_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingCrossoverFormula : PeriodicGraph Vertex →
      List (EmbeddedClause
        (Sum CrossingBoundary
          (CrossingRecord × CrossoverInternal)))) := by
  exact crossoverFamily_primrec
    (fun graph : PeriodicGraph Vertex => orientedCrossingHalo graph)
    (fun (_graph : PeriodicGraph Vertex) crossing =>
      crossingPorts crossing)
    (fun (_graph : PeriodicGraph Vertex) crossing =>
      crossingMacroOrigin crossing)
    (fun _ => 1)
    orientedCrossingHalo_primrec
    (crossingPorts_primrec.comp Primrec.snd)
    (crossingMacroOrigin_primrec.comp Primrec.snd)
    (Primrec.const 1)

theorem drawingCarrierNodeCrossoverFormula_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingCarrierNodeCrossoverFormula :
      PeriodicGraph Vertex →
        List (EmbeddedClause
          (Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))) := by
  exact crossoverFamily_primrec
    (fun graph : PeriodicGraph Vertex => orientedCrossingHalo graph)
    (fun (_graph : PeriodicGraph Vertex) crossing =>
      carrierNodeCrossingPorts crossing)
    (fun (_graph : PeriodicGraph Vertex) crossing =>
      crossingMacroOrigin crossing)
    (fun _ => 1)
    orientedCrossingHalo_primrec
    (carrierNodeCrossingPorts_primrec.comp Primrec.snd)
    (crossingMacroOrigin_primrec.comp Primrec.snd)
    (Primrec.const 1)

theorem drawingCarrierNodeCrossoverFormula_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (drawingCarrierNodeCrossoverFormula :
      PeriodicGraph Vertex →
        List (EmbeddedClause
          (Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))) :=
  drawingCarrierNodeCrossoverFormula_primrec.to_comp

theorem retainedScopedDrawingRouteWireFormula_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedScopedDrawingRouteWireFormula :
      PeriodicGraph Vertex →
        List (EmbeddedClause
          (Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))) := by
  have rename : Primrec₂ fun (_graph : PeriodicGraph Vertex)
      (clause : EmbeddedClause CarrierNode) =>
      clause.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode (CrossingRecord × CrossoverInternal)) := by
    change Primrec fun input :
        PeriodicGraph Vertex × EmbeddedClause CarrierNode =>
      input.2.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode (CrossingRecord × CrossoverInternal))
    exact EmbeddedClause.rename_primrec
      (fun (_graph : PeriodicGraph Vertex) node =>
        (Sum.inl node :
          Sum CarrierNode (CrossingRecord × CrossoverInternal)))
      (Primrec.sumInl.comp Primrec.snd)
  exact (Primrec.list_map
    retainedDrawingRouteWireFormula_primrec rename).of_eq fun _ => rfl

theorem retainedDrawingRoutePlanarCoreFormula_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingRoutePlanarCoreFormula :
      PeriodicGraph Vertex →
        List (EmbeddedClause
          (Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))) :=
  Primrec.list_append.comp
    drawingCarrierNodeCrossoverFormula_primrec
    retainedScopedDrawingRouteWireFormula_primrec

theorem retainedDrawingRoutePlanarCoreFormula_computable
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Computable (retainedDrawingRoutePlanarCoreFormula :
      PeriodicGraph Vertex →
        List (EmbeddedClause
          (Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))) :=
  retainedDrawingRoutePlanarCoreFormula_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes

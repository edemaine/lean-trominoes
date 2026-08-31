/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNextSliceData
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Named numeric and semantic retained-carrier geometries -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace CarrierFallbackRouteTailRecords

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PlanarThreeSAT

/-- Geometry projected from one selected pair of compiler rank data. -/
def Geometry.ofRankDatums
    (first second : CarrierNodeRankDatum) : Geometry where
  horizontal := first.horizontal
  nextSlice := first.pairNextSlice second
  span := (second.orderCoordinate - first.orderCoordinate).toNat

/-- The same geometry projected directly from a physical node pair at an
explicit drawing period. -/
def Geometry.ofNodePairAtPeriod
    (period : Nat) (pair : CarrierNode × CarrierNode) : Geometry where
  horizontal := pair.1.isHorizontal
  nextSlice := carrierNodePairNextSliceAtPeriod period pair
  span := (carrierNodeOrderCoordinateAtPeriod period pair.2 -
    carrierNodeOrderCoordinateAtPeriod period pair.1).toNat

/-- Semantic finite geometry of one retained carrier link. -/
def Geometry.ofLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) : Geometry where
  horizontal := link.first.isHorizontal
  nextSlice := carrierLinkNextSlice source link
  span := (AxisDirection.axisSpan
    (CarrierNode.position source.incidenceGraph link.first)
    (CarrierNode.position source.incidenceGraph link.second)).toNat

end CarrierFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes

/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordBlockData
import LeanTrominoes.PeriodicThreeSATThree

/-! # Finite geometry of final retained-carrier routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

/-- The finite compiler geometry of a semantic retained carrier.  The route
word depends only on the axis and span; `nextSlice` is supplied separately so
the same object can later carry the exact clause-profile bit. -/
def finalCarrierRouteGeometryAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool) :
    CarrierFallbackRouteTailRecords.Geometry :=
  let retained := PeriodicThreeSATThree.formula source
  { horizontal := taggedLink.1.first.isHorizontal
    nextSlice := nextSlice
    span := (AxisDirection.axisSpan
      (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
      (CarrierNode.position retained.incidenceGraph taggedLink.1.second)).toNat }

/-- Coercing the finite carrier span back to an integer recovers the actual
unsigned endpoint span. -/
theorem finalCarrierRouteGeometryAt_span_coe_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool) :
    let retained := PeriodicThreeSATThree.formula source
    ((finalCarrierRouteGeometryAt source taggedLink nextSlice).span : Int) =
      AxisDirection.axisSpan
        (CarrierNode.position retained.incidenceGraph taggedLink.1.first)
        (CarrierNode.position retained.incidenceGraph taggedLink.1.second) := by
  dsimp [finalCarrierRouteGeometryAt]
  rw [Int.toNat_of_nonneg]
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

end PeriodicEightOccurrenceSplit
end LeanTrominoes

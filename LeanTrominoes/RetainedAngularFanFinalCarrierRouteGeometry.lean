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
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
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

/-- The local implication-clause index selected by the tagged carrier side. -/
def finalCarrierLocalClauseIndex
    (taggedLink : EqualityLink CarrierNode × Bool) : Fin 2 :=
  if taggedLink.2 then 0 else 1

@[simp] theorem finalCarrierRouteGeometryAt_horizontal
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool) :
    (finalCarrierRouteGeometryAt source taggedLink nextSlice).horizontal =
      taggedLink.1.first.isHorizontal := rfl

@[simp] theorem finalCarrierRouteGeometryAt_nextSlice
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool) :
    (finalCarrierRouteGeometryAt source taggedLink nextSlice).nextSlice =
      nextSlice := rfl

@[simp] theorem finalCarrierLocalClauseIndex_val
    (taggedLink : EqualityLink CarrierNode × Bool) :
    (finalCarrierLocalClauseIndex taggedLink).val =
      if taggedLink.2 then 0 else 1 := by
  unfold finalCarrierLocalClauseIndex
  split <;> rfl

/-- Coercing the finite carrier span back to an integer recovers the actual
unsigned endpoint span. -/
theorem finalCarrierRouteGeometryAt_span_coe_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool) :
    ((finalCarrierRouteGeometryAt source taggedLink nextSlice).span : Int) =
      AxisDirection.axisSpan
        (CarrierNode.position
          (PeriodicThreeSATThree.formula source).incidenceGraph
          taggedLink.1.first)
        (CarrierNode.position
          (PeriodicThreeSATThree.formula source).incidenceGraph
          taggedLink.1.second) := by
  dsimp [finalCarrierRouteGeometryAt]
  rw [Int.toNat_of_nonneg]
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Reading the equality-lens terminal table through the actual integral span
or through the finite carrier geometry gives the same datum. -/
theorem carrierLensRouteTerminalData_finalCarrierRouteGeometryAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (nextSlice : Bool)
    (literalIndex : Nat) :
    carrierLensRouteTerminalData taggedLink.1.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.first)
          (CarrierNode.position
            (PeriodicThreeSATThree.formula source).incidenceGraph
            taggedLink.1.second))
        (if taggedLink.2 then 0 else 1) literalIndex =
      carrierLensRouteTerminalData
        (finalCarrierRouteGeometryAt source taggedLink nextSlice).horizontal
        (finalCarrierRouteGeometryAt source taggedLink nextSlice).span
        (finalCarrierLocalClauseIndex taggedLink) literalIndex := by
  rw [finalCarrierRouteGeometryAt_span_coe_eq,
    finalCarrierRouteGeometryAt_horizontal,
    finalCarrierLocalClauseIndex_val]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

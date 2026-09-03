/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceTailData
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

/-! # Figure 9 source tails follow the geometric route ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineSourceTail

open FormulaShapeDirectionOrdering
open Gadget

/-- The dynamic Figure 9 tail table is exactly the source-route tail column
after applying the same stable clockwise sort used by the positioned
geometric construction. -/
theorem orderedTailDirections_eq_clauseLiteralOrder_map
    {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    orderedTailDirections routes clauseIndex clause =
      (PositionedPeriodicCNF.clauseLiteralOrder
        routes clauseIndex clause).map fun taggedLiteral =>
          unitSubdivisionDirections
            (routes clauseIndex taggedLiteral.2).tail := by
  let annotate : PeriodicLiteral Variable × Nat → AnnotatedTail :=
    fun taggedLiteral =>
      { profile := literalProfile taggedLiteral.1
        firstDirection := AxisDirection.polylineFirstDirection
          (routes clauseIndex taggedLiteral.2)
        sourceTailDirections := unitSubdivisionDirections
          (routes clauseIndex taggedLiteral.2).tail }
  have sortedMap := List.map_insertionSort
    (r := PositionedPeriodicCNF.clauseLiteralDirectionLE
      routes clauseIndex)
    (s := directionLE)
    annotate clause.literals.zipIdx (by
      intro first _firstMember second _secondMember
      rfl)
  unfold orderedTailDirections orderedAnnotatedTails annotatedTails
    PositionedPeriodicCNF.clauseLiteralOrder
  change
    (((clause.literals.zipIdx.map annotate).insertionSort directionLE).map
        AnnotatedTail.sourceTailDirections) = _
  rw [← sortedMap, List.map_map]
  rfl

/-- Equivalently, the tail row can be read at consecutive literal indices
from the route family reindexed by the clockwise clause ordering. -/
theorem orderedTailDirections_eq_map_range_orderRoutes
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    orderedTailDirections routes clauseIndex clause =
      (List.range clause.literals.length).map fun literalIndex =>
        unitSubdivisionDirections
          (PositionedPeriodicCNF.orderRoutesByClauseDirection
            source routes clauseIndex literalIndex).tail := by
  rw [orderedTailDirections_eq_clauseLiteralOrder_map]
  let ordered := PositionedPeriodicCNF.clauseLiteralOrder
    routes clauseIndex clause
  apply List.ext_getElem
  · simp [PositionedPeriodicCNF.clauseLiteralOrder]
  · intro index leftIndexLt rightIndexLt
    have orderedIndexLt : index < ordered.length := by
      simpa [ordered] using leftIndexLt
    have concreteIndexLt : index <
        (PositionedPeriodicCNF.clauseLiteralOrder
          routes clauseIndex clause).length := by
      simpa [ordered] using orderedIndexLt
    simp only [List.getElem_map, List.getElem_range]
    unfold PositionedPeriodicCNF.orderRoutesByClauseDirection
    rw [clauseLookup]
    change unitSubdivisionDirections
        (routes clauseIndex
          (PositionedPeriodicCNF.clauseLiteralOrder
            routes clauseIndex clause)[index].2).tail =
      unitSubdivisionDirections
        (match (PositionedPeriodicCNF.clauseLiteralOrder
            routes clauseIndex clause)[index]? with
        | none => []
        | some taggedLiteral =>
            routes clauseIndex taggedLiteral.2).tail
    have indexLookup :
        (PositionedPeriodicCNF.clauseLiteralOrder
          routes clauseIndex clause)[index]? =
            some
              (PositionedPeriodicCNF.clauseLiteralOrder
                routes clauseIndex clause)[index] :=
      List.getElem?_eq_getElem concreteIndexLt
    rw [indexLookup]

/-- The whole-period anchor translation used by the canonical clockwise
route family does not alter any tail-direction row. -/
theorem orderedTailDirections_eq_map_range_orderCanonicalRoutes
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    orderedTailDirections routes clauseIndex clause =
      (List.range clause.literals.length).map fun literalIndex =>
        unitSubdivisionDirections
          (PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
            source placement routes clauseIndex literalIndex).tail := by
  rw [orderedTailDirections_eq_map_range_orderRoutes
    source routes clauseIndex clause clauseLookup]
  apply List.map_congr_left
  intro literalIndex _literalIndexMember
  unfold PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection
  rw [clauseLookup]
  let offset := placement.translation
    (Cell.sub
      (PeriodicCNF.clauseAnchor clause.literals)
      (PeriodicCNF.clauseAnchor
        (PositionedPeriodicCNF.orderClauseByRouteDirection
          routes clauseIndex clause).literals))
  change unitSubdivisionDirections
      (PositionedPeriodicCNF.orderRoutesByClauseDirection
        source routes clauseIndex literalIndex).tail =
    unitSubdivisionDirections
      (PeriodicOrthocrossing.translatePolyline offset
        (PositionedPeriodicCNF.orderRoutesByClauseDirection
          source routes clauseIndex literalIndex)).tail
  rw [show
    (PeriodicOrthocrossing.translatePolyline offset
      (PositionedPeriodicCNF.orderRoutesByClauseDirection
        source routes clauseIndex literalIndex)).tail =
      PeriodicOrthocrossing.translatePolyline offset
        (PositionedPeriodicCNF.orderRoutesByClauseDirection
          source routes clauseIndex literalIndex).tail by
    cases PositionedPeriodicCNF.orderRoutesByClauseDirection
      source routes clauseIndex literalIndex <;> rfl]
  simp

end FormulaShapeFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes

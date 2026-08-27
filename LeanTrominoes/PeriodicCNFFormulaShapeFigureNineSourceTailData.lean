/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData

/-! # Stable clockwise source-tail data for Figure 9 -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineSourceTail

open Gadget
open UnaryProgramClauseProfile
open FormulaShapeDirectionOrdering

/-- One source literal together with the finite descriptor key used for
clockwise ordering and the dynamic route word after deleting its clause-side
point. -/
structure AnnotatedTail where
  profile : LiteralProfile
  firstDirection : AxisDirection
  sourceTailDirections : List AxisDirection
  deriving DecidableEq

/-- The finite ordering key shared with direction-aware formula shapes. -/
def AnnotatedTail.key (tail : AnnotatedTail) :
    LiteralProfile × AxisDirection :=
  (tail.profile, tail.firstDirection)

/-- Stable clockwise comparison, intentionally independent of the dynamic
tail word. -/
def directionLE (first second : AnnotatedTail) : Prop :=
  FormulaShapeDirectionOrdering.directionLE first.key second.key

instance : DecidableRel directionLE := by
  intro first second
  unfold directionLE
  infer_instance

/-- Annotate every literal of one positioned clause in presentation order. -/
def annotatedTails {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    List AnnotatedTail :=
  clause.literals.zipIdx.map fun taggedLiteral =>
    let route := routes clauseIndex taggedLiteral.2
    { profile :=
        FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1
      firstDirection := AxisDirection.polylineFirstDirection route
      sourceTailDirections := unitSubdivisionDirections route.tail }

/-- Sort the literal/tail records by the exact same stable finite key used
to form the clockwise source clause. -/
def orderedAnnotatedTails {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    List AnnotatedTail :=
  (annotatedTails routes clauseIndex clause).insertionSort directionLE

/-- Dynamic tails in clockwise source-literal order. -/
def orderedTailDirections {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    List (List AxisDirection) :=
  (orderedAnnotatedTails routes clauseIndex clause).map
    AnnotatedTail.sourceTailDirections

/-- Erasing the dynamic tails recovers exactly the ordinary direction-aware
literal annotation before sorting. -/
@[simp] theorem annotatedTails_map_key {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    (annotatedTails routes clauseIndex clause).map AnnotatedTail.key =
      FormulaShapeDirectionOrdering.annotatedLiterals
        routes clauseIndex clause := by
  simp [annotatedTails, FormulaShapeDirectionOrdering.annotatedLiterals,
    AnnotatedTail.key]

/-- The paired dynamic-tail sort projects to the established stable
clockwise literal/direction sort. -/
@[simp] theorem orderedAnnotatedTails_map_key {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    (orderedAnnotatedTails routes clauseIndex clause).map AnnotatedTail.key =
      (FormulaShapeDirectionOrdering.annotatedLiterals
        routes clauseIndex clause).insertionSort
          FormulaShapeDirectionOrdering.directionLE := by
  let source := annotatedTails routes clauseIndex clause
  have mappedSort := List.map_insertionSort
    (r := directionLE)
    (s := FormulaShapeDirectionOrdering.directionLE)
    AnnotatedTail.key source (by
      intro first firstMember second secondMember
      rfl)
  unfold orderedAnnotatedTails
  rw [mappedSort]
  simp only [source, annotatedTails_map_key]

/-- Sorting and projecting preserve exactly one dynamic tail per source
literal. -/
@[simp] theorem orderedTailDirections_length {Variable : Type}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex : Nat) (clause : PositionedPeriodicClause Variable) :
    (orderedTailDirections routes clauseIndex clause).length =
      clause.literals.length := by
  simp [orderedTailDirections, orderedAnnotatedTails, annotatedTails]

end FormulaShapeFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes
